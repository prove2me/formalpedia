-- Prove2me | solution 1 for GlobalTheory.CoprimeBasisExistence.exists_basis_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:14:25.076701+00:00
-- url     : https://prove2.me/submissions/1cc7ef38-2352-4fb5-aa3e-0bf379ddf7f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IsPrincipalIdealRingLoc
import Theorems.Thm_GlobalTheory_CoprimeBasisExistence_coprimeSet_le
import Theorems.Thm_GlobalTheory_CoprimeBasisExistence_isPrincipalIdealRing_loc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CoprimeBasisExistence
open NumberField nonZeroDivisors
namespace GlobalTheory.CoprimeBasisExistence
theorem _root_.solution {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (m : ℕ) (hm : 0 < m)
    (L : Submodule (𝓞 K) V) (hL : L.FG) :
    ∃ (r : ℕ) (b : Fin r → V), LinearIndependent K b ∧ (∀ i, b i ∈ L) ∧
      ∀ w ∈ L, ∃ k : ℕ, Nat.Coprime k m ∧ k • w ∈ Submodule.span (𝓞 K) (Set.range b) := by
  classical
  have hS := coprimeSet_le (𝓞 K) m
  set R := Localization.subalgebra K (coprimeSet (𝓞 K) m) hS with hR
  have : IsPrincipalIdealRing R := isPrincipalIdealRing_loc (K := K) m hm R
  have hst : IsScalarTower (𝓞 K) R V := ⟨fun a r v => by
    change ((a • (r : K)) • v) = a • ((r : K) • v)
    rw [smul_assoc]⟩

  have key : ∀ (M : Submodule (𝓞 K) V) (v : V), v ∈ Submodule.span R (M : Set V) →
      ∃ k : ℕ, 0 < k ∧ k.Coprime m ∧ k • v ∈ M := by
    intro M v hv
    induction hv using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_pos, by simp, by simpa using hx⟩
    | zero => exact ⟨1, one_pos, by simp, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, ha', hx⟩ := hx
      obtain ⟨b, hb, hb', hy⟩ := hy
      refine ⟨a * b, mul_pos ha hb, Nat.Coprime.mul_left ha' hb', ?_⟩
      rw [smul_add]
      refine M.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact M.nsmul_mem hx b
      · rw [mul_smul]; exact M.nsmul_mem hy a
    | smul r x _ hx =>
      obtain ⟨a, ha, ha', hx⟩ := hx
      obtain ⟨⟨c, _, b, hb, hb', rfl⟩, hc⟩ := IsLocalization.surj (coprimeSet (𝓞 K) m) r
      refine ⟨a * b, mul_pos ha hb, Nat.Coprime.mul_left ha' hb', ?_⟩
      have h1 : (a * b) • r • x = c • (a • x) := by
        simp only [map_natCast] at hc
        rw [← algebraMap_smul R c, ← hc, mul_smul, smul_comm a, smul_comm a, mul_smul,
          Nat.cast_smul_eq_nsmul, smul_comm b r]
      rw [h1]
      exact M.smul_mem c hx
  let N : Submodule R V := Submodule.span R (L : Set V)
  have hN : N.FG := by
    obtain ⟨s, hs⟩ := hL
    refine ⟨s, ?_⟩
    simp only [N, ← hs]
    exact (Submodule.span_span_of_tower (𝓞 K) R (s : Set V)).symm
  have : Module.Finite R N := Module.Finite.iff_fg.mpr hN
  have : Module.IsTorsionFree R V := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r v h => ?_
    change (r : K) • v = 0 at h
    rcases smul_eq_zero.mp h with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr h
  obtain ⟨r, e⟩ := Module.basisOfFiniteTypeTorsionFree' (R := R) (M := N)
  choose k hk hk' hkL using fun i => key L (e i : V) (e i).2
  refine ⟨r, fun i => k i • (e i : V), ?_, hkL, ?_⟩
  · have h1 : LinearIndependent R (fun i => (e i : V)) :=
      e.linearIndependent.map' N.subtype N.ker_subtype
    have h2 : LinearIndependent K (fun i => (e i : V)) :=
      (LinearIndependent.iff_fractionRing R K).mp h1
    have h3 := h2.units_smul (fun i => Units.mk0 (k i : K) (Nat.cast_ne_zero.mpr (hk i).ne'))
    convert h3 using 1
    funext i
    simp [Units.smul_def, Nat.cast_smul_eq_nsmul]
  · intro w hw
    have hwN : w ∈ N := Submodule.subset_span hw
    have h1 : w ∈ Submodule.span R
        ((Submodule.span (𝓞 K) (Set.range fun i => k i • (e i : V)) : Submodule (𝓞 K) V) : Set V) := by
      have h2 : w = ∑ i, e.repr ⟨w, hwN⟩ i • (e i : V) := by
        have := congrArg Subtype.val (e.sum_repr ⟨w, hwN⟩)
        rw [Submodule.coe_sum] at this
        exact this.symm
      rw [h2]
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
      have hu : IsUnit (k i : R) := by
        have := IsLocalization.map_units R
          (⟨(k i : 𝓞 K), k i, hk i, hk' i, rfl⟩ : coprimeSet (𝓞 K) m)
        simpa using this
      obtain ⟨u, hu⟩ := hu
      have h3 : (e i : V) = ((u⁻¹ : Rˣ) : R) • (k i • (e i : V)) := by
        rw [← Nat.cast_smul_eq_nsmul R, ← hu, ← mul_smul, Units.inv_mul, one_smul]
      rw [h3]
      exact Submodule.smul_mem _ _
        (Submodule.subset_span (Submodule.subset_span ⟨i, rfl⟩))
    obtain ⟨a, -, ha, h⟩ := key _ w h1
    exact ⟨a, ha, h⟩
end GlobalTheory.CoprimeBasisExistence

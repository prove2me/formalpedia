-- Prove2me | solution 1 for GlobalTheory.OrderBasis.exists_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:07:27.903944+00:00
-- url     : https://prove2.me/submissions/bbe32385-8562-4f4c-8b26-af5a9ad4f6d0

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsBasisFgMaximalOrderSpanningFree
import Theorems.Thm_GlobalTheory_OrderBasis_exists_basis_pi
import Theorems.Thm_GlobalTheory_OrderBasis_exists_common
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.OrderBasis
namespace GlobalTheory.OrderBasis
theorem _root_.solution {E : Type} [CommRing E] (R : Subring E) [IsPrincipalIdealRing R]
    (hD : ∀ x : E, ∃ d ∈ R, IsUnit d ∧ d * x ∈ R) {V : Type} [AddCommGroup V] [Module E V]
    {m : ℕ} (y : Fin m → V) (hy : LinearIndependent E y) (Q : Submodule R V) (hQ : Q.FG)
    (hs : Submodule.span E (Q : Set V) = Submodule.span E (Set.range y)) :
    ∃ b : Fin m → V, LinearIndependent E b ∧ Q = Submodule.span R (Set.range b) := by
  let φ : (Fin m → E) →ₗ[E] V := Fintype.linearCombination E y
  have hφ : Function.Injective φ := hy.fintypeLinearCombination_injective
  have hr : ∀ q ∈ Q, ∃ v, φ v = q := by
    intro q hq
    have : q ∈ Submodule.span E (Set.range y) := hs ▸ Submodule.subset_span hq
    rw [← Fintype.range_linearCombination] at this
    exact this
  have hmap : (Q.comap (φ.restrictScalars R)).map (φ.restrictScalars R) = Q :=
    Submodule.map_comap_eq_self fun q hq => hr q hq
  have hfg : (Q.comap (φ.restrictScalars R)).FG :=
    Submodule.fg_of_fg_map_injective (φ.restrictScalars R) hφ (by rw [hmap]; exact hQ)
  obtain ⟨k, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  obtain ⟨s, -, hsu, hs1⟩ := exists_common R (fun (p : Fin k × Fin m) d => d * g p.1 p.2 ∈ R)
    (fun p d c hc h => by rw [mul_assoc]; exact R.mul_mem hc h) (fun p => hD _)
  have hsp : ∀ x ∈ Submodule.span E (Q : Set V), ∃ d ∈ R, IsUnit d ∧ d • x ∈ Q := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact ⟨1, R.one_mem, isUnit_one, by simpa using hx⟩
    | zero => exact ⟨1, R.one_mem, isUnit_one, by simp⟩
    | add x z _ _ hx hz =>
      obtain ⟨d, hd, hdu, hx⟩ := hx
      obtain ⟨e, he, heu, hz⟩ := hz
      refine ⟨d * e, R.mul_mem hd he, hdu.mul heu, ?_⟩
      have : (d * e) • (x + z) = (⟨e, he⟩ : R) • d • x + (⟨d, hd⟩ : R) • e • z := by
        simp only [Subring.smul_def, smul_add, smul_smul, mul_comm]
      rw [this]
      exact Q.add_mem (Q.smul_mem _ hx) (Q.smul_mem _ hz)
    | smul c x _ hx =>
      obtain ⟨d, hd, hdu, hx⟩ := hx
      obtain ⟨e, he, heu, hc⟩ := hD c
      refine ⟨d * e, R.mul_mem hd he, hdu.mul heu, ?_⟩
      have : (d * e) • (c • x) = (⟨e * c, hc⟩ : R) • d • x := by
        simp only [Subring.smul_def, smul_smul]
        congr 1; ring
      rw [this]
      exact Q.smul_mem _ hx
  obtain ⟨t, -, htu, ht1⟩ := exists_common R (fun (i : Fin m) d => d • y i ∈ Q)
    (fun i d c hc h => by rw [mul_smul]; exact Q.smul_mem (⟨c, hc⟩ : R) h)
    (fun i => hsp _ (hs ▸ Submodule.subset_span ⟨i, rfl⟩))
  obtain ⟨b, hb, hQb⟩ := exists_basis_pi R s t hsu htu m (Q.comap (φ.restrictScalars R))
    (by
      intro q hq i
      rw [← hg] at hq
      induction hq using Submodule.span_induction with
      | mem x hx => obtain ⟨l, rfl⟩ := hx; exact hs1 (l, i)
      | zero => simp
      | add x z _ _ hx hz => rw [Pi.add_apply, mul_add]; exact R.add_mem hx hz
      | smul c x _ hx =>
        have : s * (c • x) i = c * (s * x i) := by
          simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul]; ring
        rw [this]; exact R.mul_mem c.2 hx)
    (fun i => by
      show φ (Pi.single i t) ∈ Q
      simpa [φ, Fintype.linearCombination_apply_single] using ht1 i)
  refine ⟨φ ∘ b, hb.map' φ (LinearMap.ker_eq_bot.mpr hφ), ?_⟩
  rw [← hmap, hQb, Submodule.map_span, Set.range_comp]
  rfl
end GlobalTheory.OrderBasis

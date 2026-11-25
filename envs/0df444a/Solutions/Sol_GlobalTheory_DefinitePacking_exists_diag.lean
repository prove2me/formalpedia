-- Prove2me | solution 1 for GlobalTheory.DefinitePacking.exists_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:01:15.976135+00:00
-- url     : https://prove2.me/submissions/0f672792-2a0b-4e2d-8fcc-f6069cef83e0

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OneLeNormMulAbsNormSq
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal
open GlobalTheory GlobalTheory.DefinitePacking
namespace GlobalTheory.DefinitePacking
theorem _root_.solution {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm)
    (ha : ∀ x : V, x ≠ 0 → h x x ≠ 0) (s : ℕ) :
    ∀ W : Submodule K V, finrank K W ≤ s → ∃ (f : Fin s → V →ₗ[K] K) (e : Fin s → V),
      ∀ x ∈ W, h x x = ∑ i, star (f i x) * f i x * h (e i) (e i) := by
  induction s with
  | zero =>
    intro W hW
    have : W = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hW)
    subst this
    refine ⟨fun _ => 0, fun _ => 0, fun x hx => ?_⟩
    rw [Submodule.mem_bot] at hx
    simp [hx]
  | succ n ih =>
    intro W hW
    by_cases h0 : W = ⊥
    · subst h0
      refine ⟨fun _ => 0, fun _ => 0, fun x hx => ?_⟩
      rw [Submodule.mem_bot] at hx
      simp [hx]
    obtain ⟨e, heW, he⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    have hee := ha e he
    have hlt : W ⊓ LinearMap.ker (h e) < W := by
      refine lt_of_le_of_ne inf_le_left fun hc => ?_
      have : e ∈ W ⊓ LinearMap.ker (h e) := by rw [hc]; exact heW
      exact hee this.2
    have hr := Submodule.finrank_lt_finrank_of_lt hlt
    obtain ⟨f, e', hf⟩ := ih (W ⊓ LinearMap.ker (h e)) (by omega)
    let g : V →ₗ[K] K := (h e e)⁻¹ • h e
    let P : V →ₗ[K] V := LinearMap.id - g.smulRight e
    refine ⟨Fin.cons g (fun i => f i ∘ₗ P), Fin.cons e e', fun x hx => ?_⟩
    have hP : P x = x - g x • e := rfl
    have hg : g x * h e e = h e x := by
      simp only [g, LinearMap.smul_apply, smul_eq_mul]
      field_simp
    have hk : h e (P x) = 0 := by
      rw [hP, map_sub, map_smul, smul_eq_mul, hg, sub_self]
    have hk' : h (P x) e = 0 := by
      rw [← hs.eq e (P x), hk, map_zero]
    have hmem : P x ∈ W ⊓ LinearMap.ker (h e) :=
      ⟨by rw [hP]; exact W.sub_mem hx (W.smul_mem _ heW), hk⟩
    have hx' : x = P x + g x • e := by rw [hP]; abel
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, LinearMap.comp_apply]
    rw [← hf _ hmem]
    generalize P x = y at *
    generalize g x = c at *
    rw [hx']
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, hk, hk', starRingEnd_apply]
    ring
end GlobalTheory.DefinitePacking

-- Prove2me | solution 1 for GlobalTheory.PairOp.FF_FFStar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:49.152517+00:00
-- url     : https://prove2.me/submissions/5d5a8a53-c72c-4b4f-b6f7-3f646b954dd5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointOperatorIdentities
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Theorems.Thm_GlobalTheory_LatPair_FFStar_ofDual
import Theorems.Thm_GlobalTheory_LatPair_FF_apply
import Theorems.Thm_GlobalTheory_LatPair_Model_sum_char
import Theorems.Thm_GlobalTheory_LatPair_cross_up_ofDual
import Theorems.Thm_GlobalTheory_LatPair_sum_withKer
import Theorems.Thm_GlobalTheory_LatPair_sum_withLat
import Theorems.Thm_P2M_GlobalTheory_LatPair_tr__apply_bf1204b7b27f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
noncomputable section
namespace GlobalTheory.PairOp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
  {M : Type} [AddCommGroup M] [Module ℂ M]
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ)
variable {χ}
private theorem sum_subtype_ne_zero_eq_sum_sub_zero {V : Type} [Zero V] [Fintype V] [DecidableEq V] [Fintype {v : V // v ≠ 0}]
    (g : V → ℂ) : ∑ v : {v : V // v ≠ 0}, g v.1 = ∑ v, g v - g 0 := by
  rw [eq_sub_iff_add_eq, ← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : V))]
  congr 1
  exact Finset.sum_bij' (fun v _ => v.1) (fun v hv => ⟨v, Finset.ne_of_mem_erase hv⟩)
    (fun v _ => Finset.mem_erase.mpr ⟨v.2, Finset.mem_univ _⟩) (fun v _ => Finset.mem_univ _)
    (fun v _ => rfl) (fun v _ => rfl) (fun v _ => rfl)
section Adjoint
variable {A B A' B' : Module.End ℂ (Form k n ℂ)}
end Adjoint
end GlobalTheory.PairOp
end
end

set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
noncomputable section
open GlobalTheory GlobalTheory.PairOp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
  {M : Type} [AddCommGroup M] [Module ℂ M]
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ)
variable {χ}
namespace GlobalTheory.PairOp
theorem _root_.solution [Fintype n] (hχ : χ ≠ 1) (φ : Form k n M) :
    FF q χ (FFStar q χ φ) = (resCard k ^ Fintype.card n : ℂ) • φ - tr' φ := by
  classical
  funext P₁
  rw [FF_apply, Pi.sub_apply, Pi.smul_apply, tr'_apply]
  set L := P₁.ker with hL
  haveI : L.IsLattice k := by rw [hL]; infer_instance
  letI : Fintype {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0} := Fintype.ofFinite _
  letI : Fintype {x : Red L // x ≠ 0} := Fintype.ofFinite _
  letI : Fintype (Module.Dual 𝓀[k] (Red L)) := Fintype.ofFinite _
  letI : Fintype (Red L) := Fintype.ofFinite _
  letI : Fintype 𝓀[k] := Fintype.ofFinite _
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : {x : Red L // x ≠ 0}, up L q x₁ = P₁ :=
    ⟨_, congrArg Subtype.val ((kerEquiv L q).apply_symm_apply ⟨P₁, hL.symm⟩)⟩
  rw [← hx₁, sum_withLat L, sum_withKer L q]
  simp only [FFStar_ofDual, cross_up_ofDual, Finset.smul_sum, smul_smul, ← AddChar.map_add_eq_mul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  have hinner : ∀ x : {x : Red L // x ≠ 0}, ∑ f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0},
      χ (f.1 x₁.1 + -f.1 x.1) = (if x = x₁ then (resCard k : ℂ) ^ Fintype.card n else 0) - 1 := by
    intro x
    rw [sum_subtype_ne_zero_eq_sum_sub_zero (fun f : Module.Dual 𝓀[k] (Red L) => χ (f x₁.1 + -f x.1))]
    simp only [LinearMap.zero_apply, neg_zero, add_zero, AddChar.map_zero_eq_one]
    congr 1
    have e : ∀ f : Module.Dual 𝓀[k] (Red L),
        f x₁.1 + -f x.1 = Module.Dual.eval 𝓀[k] (Red L) (x₁.1 - x.1) f := by
      intro f
      simp [sub_eq_add_neg]
    simp only [e]
    rw [Model.sum_char hχ]
    have hiff : Module.Dual.eval 𝓀[k] (Red L) (x₁.1 - x.1) = 0 ↔ x = x₁ := by
      constructor
      · intro h0
        have h1 : x₁.1 - x.1 = 0 := (Module.forall_dual_apply_eq_zero_iff 𝓀[k] _).mp fun f => by
          simpa using LinearMap.congr_fun h0 f
        exact (Subtype.ext (sub_eq_zero.mp h1)).symm
      · rintro rfl
        simp
    have hcard : (Fintype.card (Module.Dual 𝓀[k] (Red L)) : ℂ) = (resCard k : ℂ) ^ Fintype.card n := by
      rw [Module.card_eq_pow_finrank (K := 𝓀[k]), Subspace.dual_finrank_eq, Red.finrank_eq]
      simp [resCard, Nat.card_eq_fintype_card]
    simp only [hiff, hcard]
  simp only [hinner, sub_smul, ite_smul, zero_smul, one_smul, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
end GlobalTheory.PairOp

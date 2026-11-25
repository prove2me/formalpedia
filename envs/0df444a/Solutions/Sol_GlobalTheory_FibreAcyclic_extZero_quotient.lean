-- Prove2me | solution 1 for GlobalTheory.FibreAcyclic.extZero_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:41:32.359162+00:00
-- url     : https://prove2.me/submissions/013e6152-c6f7-41c4-980f-1fc45e86ca55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsSMulRegularCokerDualMapOfExactFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemSmulTopOfForallMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing TensorProduct Function
open GlobalTheory GlobalTheory.FibreAcyclic
open GlobalTheory.DualCokernel
variable {R : Type} [CommRing R] [IsLocalRing R]
namespace GlobalTheory.FibreAcyclic
theorem _root_.solution [IsNoetherianRing R] (N : Ideal R) [IsRegularLocalRing (R ⧸ N)] (g : ℕ)
    (hg : (g : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ N)) (j : ℕ) (hj : j < g) : ExtZero (R := R) (R ⧸ N) j := by
  obtain ⟨xs, h, hd⟩ := exists_ofList_eq_maximalIdeal_length_eq (R ⧸ N)
  have hreg := isRegular_of_ofList_eq_maximalIdeal h hd.le
  have hlen : g ≤ xs.length := by
    rw [← hd] at hg
    exact_mod_cast hg
  let σ := Function.surjInv (Ideal.Quotient.mk_surjective (I := N))
  have hσ : ∀ a, Ideal.Quotient.mk _ (σ a) = a := Function.surjInv_eq _
  have hmap : (xs.map σ).map (algebraMap R (R ⧸ N)) = xs := by
    rw [List.map_map]
    exact List.map_id'' hσ xs
  have h1 : RingTheory.Sequence.IsRegular (R ⧸ N) (xs.map σ) := by
    rw [← hmap] at hreg
    exact ((AddEquiv.refl _).isRegular_congr <| List.forall₂_map_left_iff.mpr <|
      List.forall₂_same.mpr fun r _ => algebraMap_smul _ r).1 hreg
  refine ModuleCat.subsingleton_ext_of_exists_isRegular (maximalIdeal R) _ ?_ _ ?_ _ ?_ h1 j
    (by simp; omega)
  · rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
  · refine lt_top_iff_ne_top.2 (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (maximalIdeal_le_jacobson _)).symm
  · intro r hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    have hx' : x ∈ maximalIdeal _ := h ▸ Ideal.subset_span hx
    rw [mem_maximalIdeal, mem_nonunits_iff] at hx' ⊢
    exact fun hu => hx' (hσ x ▸ hu.map (Ideal.Quotient.mk _))
end GlobalTheory.FibreAcyclic

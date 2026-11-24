-- Prove2me | solution 1 for GlobalTheory.PairOp.vanishing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:35:10.484856+00:00
-- url     : https://prove2.me/submissions/99c02e72-0863-4957-8608-2da990c9f1fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointOperatorIdentities
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Theorems.Thm_GlobalTheory_PairOp_smul_ofDual
import Theorems.Thm_GlobalTheory_PairOp_smul_up
import Theorems.Thm_GlobalTheory_PairOp_sum_family_eq_zero
import Theorems.Thm_GlobalTheory_LatPair_Model_sum_stable_eq_zero
import Theorems.Thm_GlobalTheory_LatPair_mem_Mram
import Theorems.Thm_GlobalTheory_LatPair_scalar_smul_eq
import Theorems.Thm_GlobalTheory_LatPair_trKer_apply
import Theorems.Thm_GlobalTheory_LatPair_trLat_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
noncomputable section
open GlobalTheory GlobalTheory.PairOp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
  {M : Type} [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.PairOp
theorem _root_.solution [Fintype n] [DecidableEq n] (q : Unif k) : Vanishing k n M q where
  trLat_eq_zero φ h L _ := by
    rw [trLat_apply]
    exact Model.sum_stable_eq_zero h _ fun c P => by simp
  trKer_eq_zero φ h L _ := by
    rw [trKer_apply]
    exact Model.sum_stable_eq_zero h _ fun c P => by simp
  partial_lat φ h L _ S hS := by
    refine sum_family_eq_zero h (fun f => ofDual L f) (fun f g hfg => ?_) S fun c f hf => ?_
    · exact (latEquiv L).injective (Subtype.ext hfg)
    · exact ⟨⟨(c : 𝓀[k]) • f.1, smul_ne_zero c.ne_zero f.2⟩, hS c f _ hf rfl, (smul_ofDual L c f).symm⟩
  partial_ker φ h L _ S hS := by
    refine sum_family_eq_zero h (fun x => up L q x) (fun x y hxy => ?_) S fun c x hx => ?_
    · exact (kerEquiv L q).injective (Subtype.ext hxy)
    · exact ⟨⟨((c⁻¹ : 𝓀[k]ˣ) : 𝓀[k]) • x.1, smul_ne_zero (c⁻¹).ne_zero x.2⟩, hS c⁻¹ x _ hx rfl,
        (smul_up L q c x).symm⟩
  invariant_eq_zero π P v hv M' _ _ θ hθ := by
    classical
    letI : Fintype 𝓀[k]ˣ := Fintype.ofFinite _

    have scal : ∀ s : 𝒪[k]ˣ, ∃ g : GL n k, ∀ x : n → k, g • x = (s : 𝒪[k]) • x := by
      intro s
      refine ⟨Units.map (Matrix.scalar n : k →+* Matrix n n k).toMonoidHom
        (Units.map (algebraMap 𝒪[k] k).toMonoidHom s), fun x => ?_⟩
      ext i
      simp [Units.smul_def, Matrix.scalar_apply, Matrix.mulVec_diagonal, Algebra.smul_def]

    have stab : ∀ (g : GL n k) (s : 𝒪[k]ˣ), (∀ x : n → k, g • x = (s : 𝒪[k]) • x) →
        ∀ L : Submodule 𝒪[k] (n → k), g ∈ latStab L := by
      intro g s hg L
      open Pointwise in rw [MulAction.mem_stabilizer_iff]
      ext x
      rw [mem_smul_iff]
      have e : x = (s : 𝒪[k]) • (g⁻¹ • x) := by rw [← hg, smul_inv_smul]
      constructor
      · intro h
        rw [e]
        exact L.smul_mem _ h
      · intro h
        have e' : g⁻¹ • x = ((s⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) • x := by
          conv_rhs => rw [e]
          rw [smul_smul, Units.inv_mul, one_smul]
        rw [e']
        exact L.smul_mem _ h

    have lift : ∀ c : 𝓀[k]ˣ, ∃ s : 𝒪[k]ˣ, (Units.map (residue 𝒪[k]).toMonoidHom s)⁻¹ = c := by
      intro c
      obtain ⟨t, ht⟩ := IsLocalRing.residue_surjective ((c⁻¹ : 𝓀[k]ˣ) : 𝓀[k])
      have hu : IsUnit t := by
        by_contra hnu
        have h0 : residue 𝒪[k] t = 0 :=
          (IsLocalRing.residue_eq_zero_iff t).mpr ((IsLocalRing.mem_maximalIdeal t).mpr hnu)
        rw [ht] at h0
        exact (c⁻¹).ne_zero h0
      refine ⟨hu.unit, ?_⟩
      rw [inv_eq_iff_eq_inv]
      ext
      simp [ht]
    have hθc : ∀ c : 𝓀[k]ˣ, θ (formOf π P v (c • P)) = θ v := by
      intro c
      obtain ⟨s, hs⟩ := lift c
      obtain ⟨g, hg⟩ := scal s
      have hgP : g • P = c • P := by rw [scalar_smul_eq g s hg P, hs]
      rw [← hgP, formOf_smul]
      rcases hθ with h | h
      · exact h g (stab g s hg P.lat) v
      · exact h g (stab g s hg P.ker) v
    have hsum : ∑ c : 𝓀[k]ˣ, formOf π P v (c • P) = 0 := (mem_Mram _).mp hv P
    have h0 := congrArg θ hsum
    rw [map_sum, map_zero] at h0
    simp only [hθc, Finset.sum_const, Finset.card_univ] at h0
    have hcard : (Fintype.card 𝓀[k]ˣ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [← Nat.cast_smul_eq_nsmul ℂ] at h0
    exact (smul_eq_zero.mp h0).resolve_left hcard
end GlobalTheory.PairOp

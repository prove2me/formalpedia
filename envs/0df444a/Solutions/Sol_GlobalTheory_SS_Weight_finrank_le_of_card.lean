-- Prove2me | solution 1 for GlobalTheory.SS.Weight.finrank_le_of_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:22:03.683325+00:00
-- url     : https://prove2.me/submissions/dbae48ee-080c-4ac8-9cf6-1fa2db7e6e0a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsBasisAdaptedLatticeSubspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsNilpotentSubOneOfConjPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FinrankLeOfWeightsUnipotentSymplecticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_WeightLeAddOfTorsionPairing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Weight
open Module
open scoped TensorProduct nonZeroDivisors
namespace GlobalTheory.SS.Weight
theorem _root_.solution (l : ℕ) [hl : Fact l.Prime] {T M : Type} [AddCommGroup T]
    [Module ℤ_[l] T] [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T] [AddCommGroup M]
    (π : ℕ → T →+ M) (hker : ∀ n x, π n x = 0 ↔ ∃ y, x = l ^ n • y)
    (hfin : ∀ n, Finite {x : M // l ^ n • x = 0})
    (U : Submodule ℤ_[l] T) (H : AddSubgroup M) (hU : ∀ n, ∀ x ∈ U, π n x ∈ H) (C k : ℕ)
    (hc : ∀ n, Nat.card {x : H // l ^ n • x = 0} ≤ C * l ^ (n * k)) :
    finrank ℤ_[l] U ≤ k := by
  classical
  obtain ⟨u, snf⟩ := U.smithNormalForm (Module.Free.chooseBasis ℤ_[l] T)
  have hu : finrank ℤ_[l] U = u := by rw [finrank_eq_card_basis snf.bN, Fintype.card_fin]
  rw [hu]
  have ha : ∀ i, snf.a i ≠ 0 := by
    intro i h
    apply snf.bN.ne_zero i
    ext
    rw [snf.snf, h, zero_smul]; rfl
  obtain ⟨e, he⟩ : ∃ e : ℕ, ∀ i, snf.a i ∣ (l : ℤ_[l]) ^ e := by
    refine ⟨∑ i, (snf.a i).valuation, fun i => ?_⟩
    have h1 : snf.a i ∣ (l : ℤ_[l]) ^ (snf.a i).valuation := by
      conv_lhs => rw [PadicInt.unitCoeff_spec (ha i)]
      rw [Units.mul_left_dvd]
    exact h1.trans (pow_dvd_pow _ (Finset.single_le_sum (f := fun i => (snf.a i).valuation)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)))
  have hl0 : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  have key : ∀ n, (l ^ n) ^ u ≤ C * l ^ ((n + e) * k) := by
    intro n
    refine le_trans ?_ (hc (n + e))
    have htor : ∀ x, l ^ (n + e) • π (n + e) x = 0 := fun x => by
      rw [← map_nsmul, hker]; exact ⟨x, rfl⟩
    haveI : Finite {x : H // l ^ (n + e) • x = 0} := by
      haveI := hfin (n + e)
      refine Finite.of_injective (β := {x : M // l ^ (n + e) • x = 0})
        (fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩) ?_
      intro x y h
      exact Subtype.ext (Subtype.ext (congrArg (fun z => z.1) h))
    let v : (Fin u → Fin (l ^ n)) → U := fun c => snf.bN.equivFun.symm fun i => ((c i : ℕ) : ℤ_[l])
    let F : (Fin u → Fin (l ^ n)) → {x : H // l ^ (n + e) • x = 0} := fun c =>
      ⟨⟨π (n + e) (v c), hU _ _ (v c).2⟩, Subtype.ext (htor _)⟩
    have hF : Function.Injective F := by
      intro c c' h
      have h1 : π (n + e) ((v c - v c' : U) : T) = 0 := by
        rw [Submodule.coe_sub, map_sub, sub_eq_zero]
        exact congrArg (fun z => z.1.1) h
      obtain ⟨y, hy⟩ := (hker _ _).1 h1
      funext i
      have h2 := snf.repr_apply_embedding_eq_repr_smul (v c - v c') (i := i)
      rw [hy, map_nsmul, map_smul, map_sub] at h2
      have h3 : ∀ c, snf.bN.repr (v c) i = ((c i : ℕ) : ℤ_[l]) := fun c => by
        rw [← snf.bN.equivFun_apply]; simp only [v, LinearEquiv.apply_symm_apply]
      simp only [Finsupp.smul_apply, Finsupp.sub_apply, h3, nsmul_eq_mul, smul_eq_mul] at h2
      have h4 : (l : ℤ_[l]) ^ e * (l : ℤ_[l]) ^ n ∣
          (l : ℤ_[l]) ^ e * (((c i : ℕ) : ℤ_[l]) - ((c' i : ℕ) : ℤ_[l])) := by
        refine Dvd.dvd.trans ?_ (mul_dvd_mul_right (he i) _)
        rw [← h2]
        refine Dvd.dvd.mul_right ?_ _
        rw [← pow_add, add_comm]; simp
      have h5 := (mul_dvd_mul_iff_left (pow_ne_zero e hl0)).1 h4
      have h6 : ((l : ℤ) ^ n) ∣ (((c i : ℕ) : ℤ) - ((c' i : ℕ) : ℤ)) := by
        rw [← PadicInt.pow_p_dvd_int_iff]; simpa using h5
      have h7 := (c i).2
      have h8 := (c' i).2
      have h9 : (((c i : ℕ) : ℤ) - ((c' i : ℕ) : ℤ)) = 0 := by
        refine Int.eq_zero_of_abs_lt_dvd h6 ?_
        zify at h7 h8
        rw [abs_lt]; constructor <;> omega
      ext; omega
    have := Nat.card_le_card_of_injective F hF
    simpa using this
  by_contra hlt
  push_neg at hlt
  set n := C * l ^ (e * k) with hn
  have h1 := key n
  have h2 : l ^ n * l ^ (n * k) ≤ (l ^ n) ^ u := by
    rw [← pow_add, ← pow_mul]
    exact Nat.pow_le_pow_right hl.out.pos (by nlinarith)
  have h3 : C * l ^ ((n + e) * k) = n * l ^ (n * k) := by
    rw [add_mul, pow_add]; conv_rhs => rw [hn]
    ring
  have h4 : n < l ^ n := Nat.lt_pow_self hl.out.one_lt
  have h5 : 0 < l ^ (n * k) := pow_pos hl.out.pos _
  nlinarith
end GlobalTheory.SS.Weight

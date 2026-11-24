-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.exists_isRegular_ofList_eq_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:43.339185+00:00
-- url     : https://prove2.me/submissions/45389dba-881a-4e70-bd67-cb593db7b0e8

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDSerre
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsRegularLocalRing_isDomain
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_isRegularLocalRing_quotient
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_spanFinrank_maximalIdeal_quotient_add_one_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open IsLocalRing Ideal RingTheory.Sequence
universe u
variable {R : Type u} [CommRing R]
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution [IsRegularLocalRing R] :
    ∃ rs : List R, IsRegular R rs ∧ ofList rs = maximalIdeal R ∧
      (rs.length : WithBot ℕ∞) = ringKrullDim R := by
  suffices H : ∀ n : ℕ, ∀ (S : Type u) [CommRing S] [IsRegularLocalRing S],
      (maximalIdeal S).spanFinrank = n → ∃ rs : List S, IsRegular S rs ∧
        ofList rs = maximalIdeal S ∧ (rs.length : WithBot ℕ∞) = ringKrullDim S from H _ R rfl
  intro n
  induction n with
  | zero =>
    intro S _ _ hn
    have hfg : (maximalIdeal S).FG := (maximalIdeal S).fg_of_isNoetherianRing
    have hbot : maximalIdeal S = ⊥ := (Submodule.spanFinrank_eq_zero_iff_eq_bot hfg).mp hn
    refine ⟨[], IsRegular.nil S S, by simp [hbot], ?_⟩
    rw [← (isRegularLocalRing_iff S).mp inferInstance, hn]
    simp
  | succ n ih =>
    intro S _ _ hn
    have := IsRegularLocalRing.isDomain (R := S)
    have hfg : (maximalIdeal S).FG := (maximalIdeal S).fg_of_isNoetherianRing
    have hjac : maximalIdeal S ≤ jacobson ⊥ :=
      (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    have hsq : ¬ maximalIdeal S ≤ maximalIdeal S ^ 2 := by
      intro hle
      have : maximalIdeal S = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hfg
        (by simpa [pow_two, smul_eq_mul] using hle) hjac
      rw [this] at hn; simp at hn
    obtain ⟨x, hx, hx2⟩ := Set.not_subset.mp hsq
    have hx0 : x ≠ 0 := fun h ↦ hx2 (h ▸ zero_mem _)
    have hne : span {x} ≠ ⊤ := fun h ↦ (IsLocalRing.maximalIdeal.isMaximal S).ne_top
      (top_le_iff.mp (h ▸ (span_singleton_le_iff_mem _).mpr hx))
    have : Nontrivial (S ⧸ span {x}) := Ideal.Quotient.nontrivial_iff.mpr hne
    have : IsLocalRing (S ⧸ span {x}) := .of_surjective' _ Ideal.Quotient.mk_surjective
    obtain ⟨hreg, hdim⟩ := isRegularLocalRing_quotient hx hx2
    have hlt := spanFinrank_maximalIdeal_quotient_add_one_le hx hx2
    have hB : (maximalIdeal (S ⧸ span {x})).spanFinrank = n := by
      have h1 := (isRegularLocalRing_iff S).mp inferInstance
      have h2 := (isRegularLocalRing_iff (S ⧸ span {x})).mp hreg
      rw [← h1, ← h2, hn] at hdim
      have : ((maximalIdeal (S ⧸ span {x})).spanFinrank + 1 : ℕ) = n + 1 := by exact_mod_cast hdim
      omega
    obtain ⟨rsB, hrsB, hofB, hlenB⟩ := ih (S ⧸ span {x}) hB
    let lift : S ⧸ span {x} → S := Function.surjInv Ideal.Quotient.mk_surjective
    have hlift : ∀ b, Ideal.Quotient.mk (span {x}) (lift b) = b :=
      Function.surjInv_eq Ideal.Quotient.mk_surjective
    let rs' := rsB.map lift
    have hmap : rs'.map (Ideal.Quotient.mk (span {x})) = rsB := by
      simp [rs', List.map_map, Function.comp_def, hlift]
    refine ⟨x :: rs', ?_, ?_, ?_⟩
    · rw [isRegular_cons_iff']
      refine ⟨?_, ?_⟩
      · exact fun a b h ↦ mul_left_cancel₀ hx0 h
      · rw [hmap]
        have e0 : QuotSMulTop x S ≃ₗ[S] S ⧸ span {x} :=
          Submodule.quotEquivOfEq _ _ (by
            rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top])
        let e : QuotSMulTop x S ≃ₗ[S ⧸ span {x}] S ⧸ span {x} :=
          LinearEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective e0
        exact (e.isRegular_congr rsB).mpr hrsB
    · have h1 : (ofList rs').map (Ideal.Quotient.mk (span {x})) =
          (maximalIdeal S).map (Ideal.Quotient.mk (span {x})) := by
        rw [Ideal.map_ofList, hmap, hofB,
          map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective]
      have h2 := congrArg (Ideal.comap (Ideal.Quotient.mk (span {x}))) h1
      simp only [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker] at h2
      rw [ofList_cons, sup_comm, h2, sup_eq_left.mpr ((span_singleton_le_iff_mem _).mpr hx)]
    · rw [List.length_cons, List.length_map, ← hdim, ← hlenB]
      push_cast
      rfl
end GroundTheory.Arith.SchemeCoh

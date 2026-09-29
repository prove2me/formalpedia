-- Prove2me | solution 1 for NumberField.PlaceDecomp.exists_fundamentalClass_units_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/b176fbb9-ac40-55a7-b0da-3ef2090bb8bb

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Theorems.Thm_NumberField_PlaceDecomp_exists_localLevel_ringEquiv_adicCompletion
import Theorems.Thm_groupCohomology_isZero_H1_and_natCard_H2_and_span_map_of_iso
import Theorems.Thm_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass
import Theorems.Thm_ExtCitation_LocalLevel_isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass
import Theorems.Thm_ExtCitation_LocalLevel_exists_intermediateField_forall_mem_iff_smul_eq
import Theorems.Thm_ExtCitation_LocalLevel_finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq
import Theorems.Thm_IntermediateField_isSolvable_algEquiv_of_padic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_exists_fundamentalClass_units_adicCompletion
p2m_attr_erase "instance" "ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq"

set_option autoImplicit false

open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField.PlaceDecomp
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3

namespace C10Proof
open ExtCitation.LocalLevel

variable (q : ℕ) [Fact q.Prime]

theorem isSolvable_of_layer (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (hKL : K ≤ L)
    (hK : ∀ x : L, (x : PadicAlgCl q) ∈ K ↔ ∀ g : G, g • x = x) : Group.IsSolvable G := by
  classical
  let E : IntermediateField K (PadicAlgCl q) := IntermediateField.extendScalars hKL
  haveI hfdqE : Module.Finite ℚ_[q] E := ‹FiniteDimensional ℚ_[q] L›
  haveI : FiniteDimensional K E := Module.Finite.of_restrictScalars_finite ℚ_[q] K E

  let f : G →* (E ≃ₐ[K] E) :=
    { toFun := fun g => AlgEquiv.ofRingEquiv (f := (MulSemiringAction.toRingEquiv G L g : E ≃+* E))
        (fun k => (hK ⟨(k : PadicAlgCl q), hKL k.2⟩).1 k.2 g)
      map_one' := AlgEquiv.ext fun x => one_smul G (show L from x)
      map_mul' := fun g h => AlgEquiv.ext fun x => mul_smul g h (show L from x) }
  have hf : Function.Injective f := by
    intro g h hgh
    apply FaithfulSMul.eq_of_smul_eq_smul (α := L)
    intro x
    exact congrArg (fun e : E ≃ₐ[K] E => e x) hgh

  letI := Fintype.ofFinite G
  have hdeg : Module.finrank K E = Nat.card G := by
    have h1 := ExtCitation.LocalLevel.finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq q L G hG K hKL hK
    have h2 : Module.finrank ℚ_[q] K * Module.finrank K E = Module.finrank ℚ_[q] L :=
      Module.finrank_mul_finrank ℚ_[q] K E
    have hKpos : 0 < Module.finrank ℚ_[q] K := Module.finrank_pos
    rw [h1] at h2
    exact Nat.eq_of_mul_eq_mul_left hKpos (h2.trans (mul_comm _ _))
  have hcard : Nat.card (E ≃ₐ[K] E) = Module.finrank K E := by
    apply le_antisymm
    · rw [Nat.card_eq_fintype_card]; exact AlgEquiv.card_le
    · rw [hdeg]; exact Nat.card_le_card_of_injective f hf
  haveI : IsGalois K E := IsGalois.of_card_aut_eq_finrank K E hcard
  haveI : Group.IsSolvable (E ≃ₐ[K] E) := IntermediateField.isSolvable_algEquiv_of_padic q K E
  exact solvable_of_solvable_injective hf

end C10Proof

open C10Proof ExtCitation.LocalLevel NumberField.PlaceDecomp in
theorem solution
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (w : HeightOneSpectrum (𝓞 K)) :
    ∃ u : groupCohomology (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ) 2,
      (∀ S : Subgroup ↥(NumberField.PlaceDecomp.decomp E K w),
          CategoryTheory.Limits.IsZero (groupCohomology
            (Rep.res S.subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)) 1)) ∧
      (∀ (S : Subgroup ↥(NumberField.PlaceDecomp.decomp E K w)) [Fintype S],
          Nat.card (groupCohomology
            (Rep.res S.subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)) 2) =
            Fintype.card S) ∧
      (∀ S : Subgroup ↥(NumberField.PlaceDecomp.decomp E K w),
          Submodule.span ℤ {(groupCohomology.map S.subtype
            (𝟙 (Rep.res S.subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ))) 2).hom u} = ⊤) := by
  classical
  obtain ⟨q, hq, L', hfd, act, hfaith, actU, Φ, hG', hcompat', hΦ, hqw⟩ :=
    NumberField.PlaceDecomp.exists_localLevel_ringEquiv_adicCompletion E K w
  haveI : FiniteDimensional E K := Module.Finite.of_restrictScalars_finite ℚ E K
  haveI : Finite (decomp E K w) := inferInstance

  obtain ⟨K₀, hfd₀, hle₀, hK₀⟩ :=
    ExtCitation.LocalLevel.exists_intermediateField_forall_mem_iff_smul_eq q L' (decomp E K w) hG'
  have hBase : IsBase q L' (decomp E K w) K₀ := ⟨hle₀, hK₀⟩
  have hsolv : Group.IsSolvable (decomp E K w) := isSolvable_of_layer q L' (decomp E K w) hG' K₀ hle₀ hK₀

  obtain ⟨u', hu', -⟩ := ExtCitation.LocalLevel.existsUnique_isLocalFundamentalClass q L' (decomp E K w)
    hG' hcompat' hsolv K₀ hBase
  obtain ⟨c1, c2, c3⟩ := ExtCitation.LocalLevel.isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass
    q L' (decomp E K w) hG' hcompat' hsolv K₀ hBase u' hu'

  let ψ : (↥L')ˣ ≃* (w.adicCompletion K)ˣ := Units.mapEquiv Φ.symm.toMulEquiv
  have hψ : ∀ (g : decomp E K w) (v : (↥L')ˣ), ψ (g • v) = g • ψ v := by
    intro g v
    apply Units.ext
    show Φ.symm ((g • v : (↥L')ˣ) : L') = ((g • ψ v : (w.adicCompletion K)ˣ) : w.adicCompletion K)
    rw [hcompat', NumberField.PlaceDecomp.coe_smul_units]
    apply Φ.injective
    rw [RingEquiv.apply_symm_apply, hΦ]
    show g • (v : L') = g • Φ (Φ.symm (v : L'))
    rw [RingEquiv.apply_symm_apply]
  let eL : Additive (↥L')ˣ ≃ₗ[ℤ] Additive (w.adicCompletion K)ˣ := (MulEquiv.toAdditive ψ).toIntLinearEquiv
  let eR : (Representation.ofMulDistribMulAction (decomp E K w) (↥L')ˣ).Equiv
      (Representation.ofMulDistribMulAction (decomp E K w) (w.adicCompletion K)ˣ) :=
    Representation.Equiv.mk eL (fun g => by
      apply LinearMap.ext
      intro a
      show eL (Additive.ofMul (g • a.toMul)) = Additive.ofMul (g • (eL a).toMul)
      show Additive.ofMul (ψ (g • a.toMul)) = Additive.ofMul (g • ψ a.toMul)
      rw [hψ])
  let e : Rep.ofMulDistribMulAction (decomp E K w) (↥L')ˣ ≅ Rep.ofMulDistribMulAction (decomp E K w) (w.adicCompletion K)ˣ :=
    Rep.mkIso eR
  exact ⟨_, groupCohomology.isZero_H1_and_natCard_H2_and_span_map_of_iso _ _ e u' c1 c2 c3⟩

end S_NumberField_PlaceDecomp_exists_fundamentalClass_units_adicCompletion
end P2MW
export P2MW.S_NumberField_PlaceDecomp_exists_fundamentalClass_units_adicCompletion (solution)

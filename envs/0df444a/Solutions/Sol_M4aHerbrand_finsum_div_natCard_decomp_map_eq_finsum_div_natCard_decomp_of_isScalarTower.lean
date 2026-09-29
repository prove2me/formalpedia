-- Prove2me | solution 1 for M4aHerbrand.finsum_div_natCard_decomp_map_eq_finsum_div_natCard_decomp_of_isScalarTower
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/3e291b89-3be1-52ff-aa03-9a74927689b5

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_M4aHerbrand_div_natCard_decomp_eq_div_natCard_decomp_under_of_map_map_eq_zsmul_of_isScalarTower
import Theorems.Thm_M4aHerbrand_exists_map_prG_eq_zsmul_of_map_prG_eq_zsmul_of_under_eq
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_under_under_ringOfIntegers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_finsum_div_natCard_decomp_map_eq_finsum_div_natCard_decomp_of_isScalarTower
p2m_attr_erase "instance" "ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
p2m_open "CategoryTheory NumberField IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_finsum_div_natCard_decomp_map_eq_finsum_div_natCard_decomp_of_isScalarTower.M4aHerbrand"
open scoped NumberField.PlaceDecomp

namespace M4aHerbrand
p2m_export "M4aHerbrand" "finPart IdeleGaloisDescent GenuineDescent.genuineBaseChange div_natCard_decomp_eq_div_natCard_decomp_under_of_map_map_eq_zsmul_of_isScalarTower exists_map_prG_eq_zsmul_of_map_prG_eq_zsmul_of_under_eq"
namespace InfLocalSumProof
p2m_open "M4aHerbrand"

open NumberField.PlaceDecomp NumberField.PlaceAbove

theorem under_above (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (v : HeightOneSpectrum (𝓞 E)) :
    (above E K v).under (𝓞 E) = v :=
  HeightOneSpectrum.ext (by rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def]; exact comap_above E K v)

end M4aHerbrand.InfLocalSumProof

open M4aHerbrand.InfLocalSumProof NumberField.PlaceDecomp NumberField.PlaceAbove in

theorem solution
    (E F M : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field M] [NumberField M]
    [Algebra E F] [Algebra E M] [Algebra F M] [IsScalarTower E F M] [IsGalois E F] [IsGalois E M]
    (D : IdeleGaloisDescent (𝓞 F) E F) (DM : IdeleGaloisDescent (𝓞 M) E M)

    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    [MulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ]
    (hactIM : ∀ (g : (M ≃ₐ[E] M)) (x : (AdeleRing (𝓞 M) M)ˣ), g • x = DM.unitsAct g x)

    (S : Subgroup (M ≃ₐ[E] M)) [S.Normal] (ι : (M ≃ₐ[E] M) ⧸ S ≃* (F ≃ₐ[E] F))
    (hι : ∀ (g : M ≃ₐ[E] M) (x : F), algebraMap F M (ι (QuotientGroup.mk g) x) = g (algebraMap F M x))

    (J : Rep.res (ι.toMonoidHom.comp (QuotientGroup.mk' S)) (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
          Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ)
    (_ : ∀ x : (AdeleRing (𝓞 F) F)ˣ, J.hom (Additive.ofMul x) =
        Additive.ofMul (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange F M).β.toMonoidHom x))
    (y : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2))

    (prG : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (_ : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))

    (q : HeightOneSpectrum (𝓞 E) → ℕ) (_ : ∀ v, Fact (q v).Prime)
    (L' : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
    (_ : ∀ v, FiniteDimensional ℚ_[q v] (L' v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (L' v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ)
    (Φ : ∀ v : HeightOneSpectrum (𝓞 E), (NumberField.PlaceAbove.above E F v).adicCompletion F ≃+* L' v)
    (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : ℚ_[q v]), g • algebraMap ℚ_[q v] (L' v) y = algebraMap ℚ_[q v] (L' v) y)
    (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (↥(L' v))ˣ), ((g • y : (↥(L' v))ˣ) : L' v) = g • (y : L' v))
    (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (NumberField.PlaceAbove.above E F v).adicCompletion F), (Φ v) (g • y) = g • (Φ v) y)
    (K₀ : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
    (_ : ∀ v, FiniteDimensional ℚ_[q v] (K₀ v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsBase (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v))
    (θ : ∀ v : HeightOneSpectrum (𝓞 E), Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ)
    (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (y : (↥(L' v))ˣ),
      ((Additive.toMul ((θ v).hom (Additive.ofMul y)) : ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ) : (NumberField.PlaceAbove.above E F v).adicCompletion F) =
        (Φ v).symm (y : L' v))
    (u' : ∀ v : HeightOneSpectrum (𝓞 E), groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ))
    (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsLocalFundamentalClass (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v) (u' v))

    (n : HeightOneSpectrum (𝓞 E) → ℤ)
    (_ : ∀ v : HeightOneSpectrum (𝓞 E),
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype (prG (NumberField.PlaceAbove.above E F v)) 2).hom y =
        n v • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (θ v) 2).hom (u' v))

    (prM : ∀ w : HeightOneSpectrum (𝓞 M),
      Rep.res (NumberField.PlaceDecomp.decomp E M w).subtype (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M w)) (w.adicCompletion M)ˣ)
    (_ : ∀ (w : HeightOneSpectrum (𝓞 M)) (x : (AdeleRing (𝓞 M) M)ˣ), (prM w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))

    (qM : HeightOneSpectrum (𝓞 E) → ℕ) (_ : ∀ v, Fact (qM v).Prime)
    (LM : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[qM v] (PadicAlgCl (qM v)))
    (_ : ∀ v, FiniteDimensional ℚ_[qM v] (LM v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) (LM v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) (↥(LM v))ˣ)
    (ΦM : ∀ v : HeightOneSpectrum (𝓞 E), (NumberField.PlaceAbove.above E M v).adicCompletion M ≃+* LM v)
    (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) (y : ℚ_[qM v]), g • algebraMap ℚ_[qM v] (LM v) y = algebraMap ℚ_[qM v] (LM v) y)
    (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) (y : (↥(LM v))ˣ), ((g • y : (↥(LM v))ˣ) : LM v) = g • (y : LM v))
    (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) (y : (NumberField.PlaceAbove.above E M v).adicCompletion M), (ΦM v) (g • y) = g • (ΦM v) y)
    (KM : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[qM v] (PadicAlgCl (qM v)))
    (_ : ∀ v, FiniteDimensional ℚ_[qM v] (KM v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsBase (qM v) (LM v) (↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) (KM v))
    (θM : ∀ v : HeightOneSpectrum (𝓞 E), Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) (↥(LM v))ˣ ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) ((NumberField.PlaceAbove.above E M v).adicCompletion M)ˣ)
    (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (y : (↥(LM v))ˣ),
      ((Additive.toMul ((θM v).hom (Additive.ofMul y)) : ((NumberField.PlaceAbove.above E M v).adicCompletion M)ˣ) : (NumberField.PlaceAbove.above E M v).adicCompletion M) =
        (ΦM v).symm (y : LM v))
    (uM : ∀ v : HeightOneSpectrum (𝓞 E), groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) (↥(LM v))ˣ))
    (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsLocalFundamentalClass (qM v) (LM v) (↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) (KM v) (uM v))

    (nM : HeightOneSpectrum (𝓞 E) → ℤ)
    (_ : ∀ v : HeightOneSpectrum (𝓞 E),
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v)).subtype (prM (NumberField.PlaceAbove.above E M v)) 2).hom ((groupCohomology.map (ι.toMonoidHom.comp (QuotientGroup.mk' S)) J 2).hom y) =
        nM v • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) (θM v) 2).hom (uM v)) :
    ∑ᶠ v : HeightOneSpectrum (𝓞 E), ((((nM v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v)) : ℚ) : ℚ) : AddCircle (1 : ℚ))) =
      ∑ᶠ v : HeightOneSpectrum (𝓞 E), ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℚ) : ℚ) : AddCircle (1 : ℚ)))  := by
  rename_i hJ hprG hqp hL'fd instL' instL'u hqalg hucompat hΦ hK₀fd hK₀ hθ hu' hn hprM hqMp hLMfd instLM instLMu hqMalg huMcompat hΦM hKMfd hKM hθM huM hnM
  apply finsum_congr
  intro v

  have hww₁ : ((above E M v).under (𝓞 F)).under (𝓞 E) = (above E F v).under (𝓞 E) := by
    rw [IsDedekindDomain.HeightOneSpectrum.under_under_ringOfIntegers E F M, under_above, under_above]

  letI := instL' v; letI := instL'u v; haveI := hqp v; haveI := hL'fd v; haveI := hK₀fd v
  obtain ⟨hcard, instA, instB, Φ₁, θ₁, u₁, hq₁, hc₁, hΦ₁, hB₁, hθ₁, hu₁, hn₁⟩ :=
    M4aHerbrand.exists_map_prG_eq_zsmul_of_map_prG_eq_zsmul_of_under_eq E F D hactI prG hprG y
      (above E F v) ((above E M v).under (𝓞 F)) hww₁ (q v) (L' v) (Φ v) (hqalg v) (hucompat v) (hΦ v) (K₀ v) (hK₀ v) (θ v) (hθ v)
      (u' v) (hu' v) (n v) (hn v)

  letI := instLM v; letI := instLMu v; haveI := hqMp v; haveI := hLMfd v; haveI := hKMfd v
  letI := instA; letI := instB
  have key := M4aHerbrand.div_natCard_decomp_eq_div_natCard_decomp_under_of_map_map_eq_zsmul_of_isScalarTower E F M S ι hι J hJ
    (above E M v) (prG ((above E M v).under (𝓞 F))) (hprG _) (prM (above E M v)) (hprM _) y
    (q v) (L' v) Φ₁ hq₁ hc₁ hΦ₁ (K₀ v) hB₁ θ₁ hθ₁ u₁ hu₁ (n v) hn₁
    (qM v) (LM v) (ΦM v) (hqMalg v) (huMcompat v) (hΦM v) (KM v) (hKM v) (θM v) (hθM v) (uM v) (huM v) (nM v) (hnM v)
  rw [key, hcard]

end S_M4aHerbrand_finsum_div_natCard_decomp_map_eq_finsum_div_natCard_decomp_of_isScalarTower
end P2MW
export P2MW.S_M4aHerbrand_finsum_div_natCard_decomp_map_eq_finsum_div_natCard_decomp_of_isScalarTower (solution)

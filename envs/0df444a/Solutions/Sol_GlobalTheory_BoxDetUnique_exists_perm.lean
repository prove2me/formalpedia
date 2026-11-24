-- Prove2me | solution 1 for GlobalTheory.BoxDetUnique.exists_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:55:31.918304+00:00
-- url     : https://prove2.me/submissions/9c8c4c1f-97e7-4e6c-8628-ecf910bbbc52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CardHomVanishingOfDiagBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DetKroneckerPower
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsBoxSec
import Theorems.Thm_GlobalTheory_card_ker_int_matrix_four
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.BoxDetUnique
variable {X Y Z : Scheme.{0}} {R : Type} [CommRing R]
namespace GlobalTheory.BoxDetUnique
theorem _root_.solution (hN : Out.MulNSt) {K : Type} [Field K] (P : Out.PolAV (Sp K)) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ)
    (hm : (m : K) ≠ 0) (hal : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
    (ξ ξ' : (Fin 4 → Fin (m ^ P.g)) → Fin 4 → (𝟙_ (Over (Sp K)) ⟶ P.A))
    (h : Function.Injective ξ) (h' : Function.Injective ξ')
    (e : ∀ I c, (List.ofFn fun r : Fin 4 => ξ I r ^ al r c).prod = 1)
    (e' : ∀ I c, (List.ofFn fun r : Fin 4 => ξ' I r ^ al r c).prod = 1) :
    ∃ σ : Equiv.Perm (Fin 4 → Fin (m ^ P.g)), ξ' = fun I => ξ (σ I) := by
  haveI := P.isAb.comm
  let k := AlgebraicClosure K
  let t : Spec (CommRingCat.of k) ⟶ Sp K := Spec.map (CommRingCat.ofHom (algebraMap K k))
  have hm1 : 1 ≤ m := Nat.pos_of_ne_zero fun h0 => hm (by rw [h0, Nat.cast_zero])
  have hc := GlobalTheory.card_ker_int_matrix_four (Over.mk t ⟶ P.A) m (2 * P.g) al hm1 hal (fun n hn => by
    have hn0 : (n : K) ≠ 0 := fun h0 => hm (by obtain ⟨d, rfl⟩ := hn; rw [Nat.cast_mul, h0, zero_mul])
    refine (hN _ P n (Nat.pos_of_ne_zero fun h0 => hn0 (by rw [h0, Nat.cast_zero]))).2.2.2.2 k t ?_
    rw [← map_natCast (algebraMap K k)]
    exact (map_ne_zero _).2 hn0)
  have hepi : Epi t := by
    haveI : Flat t := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact RingHom.flat_algebraMap_iff.2 inferInstance
    haveI : Surjective t := ⟨fun y => ⟨IsLocalRing.closedPoint k, Subsingleton.elim _ _⟩⟩
    exact Flat.epi_of_flat_of_surjective t
  let f : (𝟙_ (Over (Sp K)) ⟶ P.A) →* (Over.mk t ⟶ P.A) := preHom (toUnit (Over.mk t))
  have hf : Function.Injective f := fun a b hab => by
    have h1 : (toUnit (Over.mk t)).left ≫ a.left = (toUnit (Over.mk t)).left ≫ b.left := congrArg (·.left) hab
    have h2 : (toUnit (Over.mk t)).left = t := (Category.comp_id _).symm.trans (Over.w (toUnit (Over.mk t)))
    haveI : Epi (toUnit (Over.mk t)).left := h2 ▸ hepi
    exact Over.OverMorphism.ext ((cancel_epi _).1 h1)
  have bij : ∀ (ζ : (Fin 4 → Fin (m ^ P.g)) → Fin 4 → (𝟙_ (Over (Sp K)) ⟶ P.A)), Function.Injective ζ →
      (∀ I c, (List.ofFn fun r : Fin 4 => ζ I r ^ al r c).prod = 1) →
      ∃ E : (Fin 4 → Fin (m ^ P.g)) ≃ {ξ : Fin 4 → (Over.mk t ⟶ P.A) // ∀ c, ∏ r', ξ r' ^ al r' c = 1},
        ∀ I r, (E I).1 r = f (ζ I r) := by
    intro ζ hζ he
    let g : (Fin 4 → Fin (m ^ P.g)) → {ξ : Fin 4 → (Over.mk t ⟶ P.A) // ∀ c, ∏ r', ξ r' ^ al r' c = 1} :=
      fun I => ⟨fun r => f (ζ I r), fun c => by
        have := congrArg f (he I c)
        rw [List.prod_ofFn, map_prod, map_one] at this
        simpa only [map_zpow] using this⟩
    have hg : Function.Injective g := fun I I' hI => hζ (funext fun r => hf (congrFun (congrArg Subtype.val hI) r))
    haveI : Finite {ξ : Fin 4 → (Over.mk t ⟶ P.A) // ∀ c, ∏ r', ξ r' ^ al r' c = 1} :=
      Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
    refine ⟨Equiv.ofBijective g (hg.bijective_of_nat_card_le ?_), fun _ _ => rfl⟩
    rw [hc, Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_fin, ← pow_mul]
    exact le_of_eq (by congr 1; ring)
  obtain ⟨E, hE⟩ := bij ξ h e
  obtain ⟨E', hE'⟩ := bij ξ' h' e'
  refine ⟨E'.trans E.symm, funext fun I => funext fun r => hf ?_⟩
  rw [← hE, ← hE']
  simp
end GlobalTheory.BoxDetUnique

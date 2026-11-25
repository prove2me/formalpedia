-- Prove2me | solution 1 for GlobalTheory.FamSpan.exists_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:03:46.615026+00:00
-- url     : https://prove2.me/submissions/eeee1f2b-b331-4910-a55e-7ec758d1e12c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsRepresentativesModNsmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsBasisOfEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FamEqOnClassOfEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTwistBasisOffPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFamOfIsPullDegStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IntegralFamilyPrescribedTermUnitAtPrimeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIntegralFamiliesSpanPullDegeneration
import Theorems.Thm_GlobalTheory_FamSpan_val_of_rel
import Theorems.Thm_GlobalTheory_FamSpan_zero_sec
import Theorems.Thm_P2M_GlobalTheory_FamSpan_fam_B_comm_3ace86c881b8
import Theorems.Thm_GlobalTheory_FamSpan_span_term
import Theorems.Thm_GlobalTheory_FamSpan_sum_f
import Theorems.Thm_GlobalTheory_SecPull_existsUnique_secPull
import Theorems.Thm_GlobalTheory_T_exists_fam_of_isPullDeg_alt
import Theorems.Thm_GlobalTheory_T_integralFamily_prescribedTerm_unit_at_prime
import Theorems.Thm_GlobalTheory_TwistLoc_exists_basis_off_prime
import Theorems.Thm_GlobalTheory_exists_representatives_mod_nsmul
import Theorems.Thm_GlobalTheory_fam_eq_on_class_of_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FamSpan
open DVR
namespace GlobalTheory.FamSpan
theorem _root_.solution : PolBaseChangeSt → GlobalFnsSt → DVR.TwistBaseChangeStatement → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R), AdmBase R I → ∀ (φ : R →+* R') (D : DegData R I) (D' : DegPre R') (hD : IsPullDeg φ D.toPre D') (k : ℕ), 1 ≤ k → ∃ (n : ℕ) (F : Fin n → Fam D.toPre (FractionRing R) k) (f : Fin n → ∀ α, D.toPre.SecB k α) (F' : Fin n → Fam D' (FractionRing R') k) (f' : Fin n → ∀ α, D'.SecB k α), (∀ i, (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) ((F i).s α) (D.toPre.famφB α) (DegPre.famε k) (f i α) (DegPre.prB D.toPre (FractionRing R)).left 1) ∧ (∀ α, GeneratorPullback.SecScal D'.P.L (DegPre.famφ D' (FractionRing R') α) (DegPre.famε k) ((F' i).s α) (D'.famφB α) (DegPre.famε k) (f' i α) (DegPre.prB D' (FractionRing R')).left 1) ∧ (∀ x : D'.X, (∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (p : Fin 4 → D.toPre.P.L.ι) (q : Fin 4 → D'.P.L.ι), (∀ κ, ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) ((D'.famφB x) κ (r z)) ∈ D.toPre.P.L.U (p κ)) → (∀ κ, (D'.famφB x) κ (r z) ∈ D'.P.L.U (q κ)) → Geo.Tor.gs (r ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) z (LB.wchart D.toPre.P.L (D.toPre.famφB (hD.xe x)) p) ((f i (hD.xe x)).f p) = (∏ κ, Geo.Tor.gw hD.w (r ≫ (D'.famφB x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val * Geo.Tor.gs r z (LB.wchart D'.P.L (D'.famφB x) q) ((f' i x).f q)))) ∧ Submodule.span (FractionRing R') (Set.range F') = ⊤ := by
  intro hP hG hT R R' _ _ _ _ I hA φ D D' hD k hk
  classical
  have : IsNoetherianRing R := hA.1
  let pt : (TK R').left := genericPoint (Spec (CommRingCat.of (FractionRing R')))
  let P : Spec (CommRingCat.of R) := (jK R' ≫ specOf φ) pt
  have hPW : P ∈ hD.W := by
    show (jK R' ≫ specOf φ) pt ∈ hD.W
    rw [← hD.g_comm]
    exact (hD.g pt).2
  have hne : ∀ r : R, r ∉ P.asIdeal → algebraMap R' (FractionRing R') (φ r) ≠ 0 := fun r hr h => hr (by
    show algebraMap R' (FractionRing R') (φ r) ∈ PrimeSpectrum.asIdeal pt
    rw [h]; exact Ideal.zero_mem _)
  have hgen : genericPoint (Spec (CommRingCat.of R)) ∈ hD.W :=
    (genericPoint_specializes P).mem_open hD.W.isOpen hPW
  have := P.isPrime
  obtain ⟨-, e, he⟩ := exists_representatives_mod_nsmul D'.X k hk
  choose b hb using fun α => GlobalTheory.TwistLoc.exists_basis_off_prime hP hG hT R D.toPre ⟨hD.W, hgen, ⟨hD.psiW⟩⟩ P.asIdeal k hk α
  choose r hr F f hF hfρ hf0 using fun q : Fin (k ^ Module.finrank ℤ D'.X) × Fin (k ^ D.toPre.P.g) =>
    GlobalTheory.T.integralFamily_prescribedTerm_unit_at_prime hG R I hA D hD.W ⟨hD.psiW⟩ P hPW k hk (hD.xe (e q.1)) (b (hD.xe (e q.1)) q.2)
  choose f' hf' using fun q x => (SecPull.existsUnique_secPull _ _ _ _ D.toPre.P.L D'.P.L _ D.toPre.P.isLB D'.P.isLB
    hD.w hD.w_gen (Fin 4) (D'.famφB x) (D.toPre.famφB (hD.xe x)) (DegPre.famε k) _ (famφB_comm hD x)
    (f q (hD.xe x))).exists
  choose F' hF' using fun q => GlobalTheory.T.exists_fam_of_isPullDeg_alt hG R R' φ D.toPre D' hD k (F q) (f q) (f' q) (hF q) (hf' q)
  let en := (finProdFinEquiv (m := k ^ Module.finrank ℤ D'.X) (n := k ^ D.toPre.P.g)).symm
  refine ⟨_, fun i => F (en i), fun i => f (en i), fun i => F' (en i), fun i => f' (en i),
    fun i => ⟨hF _, hF' _, hf' _⟩, ?_⟩
  have hrange : Set.range (fun i => F' (en i)) = Set.range F' := en.surjective.range_comp F'
  rw [hrange, eq_top_iff]
  rintro s -
  choose c hc using fun i => span_term hD k (e i) (b (hD.xe (e i))) (fun l => f (i, l) (hD.xe (e i)))
    (hb _ _ _ (fun t ht => (hne t ht).isUnit) _ (fun _ _ => rfl)) (fun l => r (i, l)) (fun l => hne _ (hr (i, l)))
    (fun l => hfρ (i, l)) (fun l => f' (i, l) (e i))
    (fun l y J J' hJ hJ' => val_of_rel (famφB_comm hD (e i)) (hf' (i, l) (e i)) _ y hJ hJ')
    (fun l => (F' (i, l)).s (e i)) (fun l => hF' (i, l) (e i)) (s.s (e i))
  have hs : s = ∑ q : Fin (k ^ Module.finrank ℤ D'.X) × Fin (k ^ D.toPre.P.g), c q.1 q.2 • F' q := by
    refine fam_ext fun χ j => ?_
    obtain ⟨i, ⟨m, rfl⟩, -⟩ := he χ
    refine fam_eq_on_class_of_eq hG R' D' _ k s _ (e i) (fun j => ?_) m j
    rw [sum_f, Fintype.sum_prod_type, Finset.sum_eq_single i, hc i j]
    · rfl
    · intro i' _ hi
      refine Finset.sum_eq_zero fun l _ => ?_
      have h0 := zero_sec D.toPre.P.isLB D'.P.isLB (DegPre.prB D' (FractionRing R')).left (f (i', l) (hD.xe (e i)))
        (hf0 (i', l) _ fun mu hmu => hi ((he (e i)).unique ⟨hD.xe.symm mu, hD.xe.injective (by
          rw [map_add, map_nsmul, AddEquiv.apply_symm_apply]; exact hmu.symm)⟩ ⟨0, by rw [smul_zero, add_zero]⟩))
        (f' (i', l) (e i)) (fun y J J' hJ hJ' => val_of_rel (famφB_comm hD (e i)) (hf' (i', l) (e i)) _ y hJ hJ')
        ((F' (i', l)).s (e i)) (hF' (i', l) (e i)) j
      rw [smul_f, h0, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [hs]
  exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
end GlobalTheory.FamSpan

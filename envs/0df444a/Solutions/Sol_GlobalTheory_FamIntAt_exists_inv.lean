-- Prove2me | solution 1 for GlobalTheory.FamIntAt.exists_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:54:41.371335+00:00
-- url     : https://prove2.me/submissions/e20d6475-1234-4040-9f21-7e941fbacc49

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsFamRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PsiInOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IntegralFamilyPrescribedTermUnitAtPrime
import Theorems.Thm_GlobalTheory_FamIntAt_exists_extend
import Theorems.Thm_GlobalTheory_FamIntAt_eq_genPt
import Theorems.Thm_GlobalTheory_FamIntAt_local_inv
import Theorems.Thm_GlobalTheory_FamIntAt_sval_secScale
import Theorems.Thm_GlobalTheory_FamIntAt_gs_pow
import Theorems.Thm_GlobalTheory_PsiInPull_jK_mem
import Theorems.Thm_GlobalTheory_PsiInPull_mem_wchart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_genSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.FamIntAt
variable {R : Type} [CommRing R] [IsDomain R]
namespace GlobalTheory.FamIntAt
theorem _root_.solution {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens} (ψ : PsiOn D W) (ρ : D.X)
    (p : Spec (CommRingCat.of R)) (hp : p ∈ W) : ∃ r : R, r ∉ p.asIdeal ∧
      ∃ Φ : LB.Sec (LB.LinComb D.P.L (Y := Spec (CommRingCat.of R)) (K := PUnit) (fun _ => (D.c ρ).left)
        (fun _ => - -1)), ∀ (T : Scheme.{0}) (τ : T ⟶ (TK R).left) (z : T) (J), Good D.P.L z J →
        sval Φ (τ ≫ jK R) z J = gs (τ ≫ jK R) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) *
          ((val (D.psi ρ) τ z J)⁻¹).val := by
  classical
  obtain ⟨_, ⟨r₀, rfl⟩, hp₀, hW⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (u := W.1) hp W.isOpen
  set g : Γ(Spec (CommRingCat.of R), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r₀ with hg
  have eg : (Spec (CommRingCat.of R)).basicOpen g = PrimeSpectrum.basicOpen r₀ :=
    basicOpen_eq_of_affine (R := CommRingCat.of R) r₀
  have hgen : jK R (genPt R) ∈ (Spec (CommRingCat.of R)).basicOpen g := PsiInPull.jK_mem _ _ fun h0 =>
    (h0.le (eg.ge hp₀) : p ∈ (⊥ : (Spec (CommRingCat.of R)).Opens))
  choose j V n a hq hV ha using local_inv ψ ρ g (eg.le.trans hW) hgen
  obtain ⟨S, hS⟩ := (isCompact_univ (X := Spec (CommRingCat.of R))).elim_finite_subcover (fun q => (V q : Set (Spec (CommRingCat.of R))))
    (fun q => (V q).isOpen) (fun q _ => Set.mem_iUnion.2 ⟨q, hq q⟩)
  have hN : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (r₀ ^ (∑ q ∈ S, n q)) = g ^ (∑ q ∈ S, n q) := map_pow _ _ _
  have hc : ∀ (T : Scheme.{0}) (τ : T ⟶ (TK R).left) (z : T), gs τ z ⊤ (scal (jK R) (r₀ ^ (∑ q ∈ S, n q))) =
      gs (τ ≫ jK R) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (r₀ ^ (∑ q ∈ S, n q))) := fun T τ z =>
    gs_pull τ (jK R) z ⊤ trivial _
  obtain ⟨s, hs⟩ := exists_extend D.P.isLB (jK R) (genPt R) eq_genPt (PsiInPull.jK_mem _) (K := PUnit)
    (fun _ => (D.c ρ).left) (fun _ => - -1) (SecOps.secScale (scal (jK R) (r₀ ^ (∑ q ∈ S, n q)))
      (Geo.Tor.genSec (LB.invGen D.P.L _ _ (D.psi ρ)) (invGen_isGen _ _ _ _ (D.psi_gen ρ)))) (fun q => by
      obtain ⟨q', hq', hqq⟩ : ∃ q' ∈ S, q ∈ V q' := by simpa using hS (Set.mem_univ q)
      have hm : jK R (genPt R) ∈ V q' := PsiInPull.jK_mem _ _ fun h0 =>
        (h0.le hqq : q ∈ (⊥ : (Spec (CommRingCat.of R)).Opens))
      have hm' : (𝟙 (TK R).left : _ ⟶ _) (genPt R) ∈ LB.wchart D.P.L (fun _ : PUnit => D.xK ρ) (fun _ => j q') :=
        PsiInPull.mem_wchart _ _ _ _ (hV q' hm)
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) hq')
      refine ⟨fun _ => j q', V q', resTop _ (g ^ d) * a q', hqq,
        fun y hy => PsiInPull.mem_wchart _ _ _ _ (hV q' hy), ?_⟩
      refine ((gs_mul _ _ _ hm _ _).trans (congrArg₂ (· * ·) (gs_res _ _ le_top hm _) (ha q'))).trans
        (Eq.trans ?_ ((gs_mul _ _ _ hm' _ _).trans (congrArg₂ (· * ·) ((gs_res _ _ le_top hm' _).trans (hc _ _ _))
          ((gs_unit _ _ _ hm' _).trans (congrArg Units.val (map_inv _ _))))).symm)
      rw [hN, hd, gs_pow, gs_pow, ← _root_.mul_assoc, ← pow_add, add_comm d]
      erw [Category.id_comp]
      rfl)
  refine ⟨r₀ ^ (∑ q ∈ S, n q), fun h => hp₀ (p.isPrime.mem_of_pow_mem _ h), s, fun T τ z J hJ => ?_⟩
  refine (hs T τ z J hJ).trans ((sval_secScale _ _ τ z hJ).trans (congrArg₂ (· * ·) (hc T τ z) ?_))
  exact (sval_genSec _ _ τ z hJ).trans (congrArg Units.val (val_inv _ _))
end GlobalTheory.FamIntAt

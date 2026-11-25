-- Prove2me | solution 1 for GlobalTheory.TwistLoc.exists_basis_off_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:21:26.999515+00:00
-- url     : https://prove2.me/submissions/95d33bb6-b79b-46b2-86e1-c6087e116ea7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTwistBasisOffPrime
import Theorems.Thm_GlobalTheory_TwistLoc_exists_up_sec
import Theorems.Thm_GlobalTheory_TwistLoc_exists_clear_denominator
import Theorems.Thm_GlobalTheory_TwistLoc_basis_transport
import Theorems.Thm_GlobalTheory_TwistLoc_fam_comm
import Theorems.Thm_GlobalTheory_DegPull_exists_isPullDeg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TwistLoc
namespace GlobalTheory.TwistLoc
theorem _root_.solution : PolBaseChangeSt → GlobalFnsSt → DVR.TwistBaseChangeStatement → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : DegPre R), (∃ W : (Spec (CommRingCat.of R)).Opens, genericPoint (Spec (CommRingCat.of R)) ∈ W ∧ Nonempty (PsiOn D W)) → ∀ (p : Ideal R) [p.IsPrime] (k : ℕ), 1 ≤ k → ∀ α : D.X, ∃ b : Fin (k ^ D.P.g) → D.SecB k α, ∀ (R' : Type) [CommRing R'] (f : R →+* R'), (∀ s ∉ p, IsUnit (f s)) → ∀ b' : Fin (k ^ D.P.g) → LB.Sec (LB.LinComb D.P.L (fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left ≫ DegPre.famφB D α i) (DegPre.famε k)), (∀ i, IsPullSecLC D.P.L (DegPre.famφB D α) (DegPre.famε k) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left (b i) (b' i)) → IsSecBasis (T := Over.mk (Spec.map (CommRingCat.ofHom f))) (A := D.P.A) _ b' := by
  intro hP _ hT R _ _ _ D ⟨W, hW, hψ⟩ p _ k hk α
  let Rp := Localization.AtPrime p
  have inj : Function.Injective (algebraMap R Rp) :=
    IsLocalization.injective Rp p.primeCompl_le_nonZeroDivisors
  obtain ⟨D', hD, -, hg⟩ := DegPull.exists_isPullDeg hP R Rp (algebraMap R Rp) D W hψ (by
    have : (specOf (algebraMap R Rp)).base (genericPoint (Spec (CommRingCat.of Rp))) =
        genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      apply PrimeSpectrum.ext
      exact Ideal.comap_bot_of_injective _ inj
    rw [this]; exact hW)
  obtain ⟨α', rfl⟩ := hD.xe.surjective α
  obtain ⟨m, b₀, hm, hb₀⟩ := hT Rp D' k hk α'
  rw [hg] at hm
  subst hm
  have gp := pull_grp hD
  have hw := hD.w_gen
  have hφ := fam_comm hD α'
  generalize hD.w = w at hw
  generalize hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (algebraMap R Rp)) = F at gp w hw hφ
  have := D.P.isAb.proper
  have : CompactSpace D.P.A.left := QuasiCompact.compactSpace_of_compactSpace D.P.A.hom
  have : QuasiSeparatedSpace D.P.A.left := (quasiSeparated_iff_quasiSeparatedSpace D.P.A.hom).mp inferInstance
  choose a ha using fun i => exists_up_sec ((isGen_iff w).1 hw) D.P.isLB D'.P.isLB hφ (DegPre.famε k) (b₀ i)
  choose t ht b hb using fun i => exists_clear_denominator p.primeCompl gp.1 D.P.isLB _ _ (a i)
  refine ⟨b, fun R' _ f hf b' hb' => ?_⟩
  let g : Rp →+* R' := IsLocalization.lift (M := p.primeCompl) (g := f) fun s => hf s.1 s.2
  have hfg : Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom (algebraMap R Rp)) =
      Spec.map (CommRingCat.ofHom f) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, IsLocalization.lift_comp]
  let T₁ : Over (Spec (CommRingCat.of R)) := Over.mk (Spec.map (CommRingCat.ofHom f))
  let T₂ : Over (Spec (CommRingCat.of Rp)) := Over.mk (Spec.map (CommRingCat.ofHom g))
  have H₁ : IsPullback (snd T₁ D.P.A).left (fst T₁ D.P.A).left D.P.A.hom (Spec.map (CommRingCat.ofHom f)) :=
    (IsPullback.of_hasPullback T₁.hom D.P.A.hom).flip
  have H₂ : IsPullback ((snd T₂ D'.P.A).left ≫ F) (fst T₂ D'.P.A).left D.P.A.hom (Spec.map (CommRingCat.ofHom f)) := by
    rw [← hfg]
    exact (IsPullback.of_hasPullback T₂.hom D'.P.A.hom).flip.paste_horiz gp.1
  let θ := H₁.isoIsPullback _ _ H₂
  have θ₁ : θ.hom ≫ (snd T₂ D'.P.A).left ≫ F = (snd T₁ D.P.A).left := H₁.isoIsPullback_hom_fst _ _ H₂
  have θ₂ : θ.hom ≫ (fst T₂ D'.P.A).left = (fst T₁ D.P.A).left := H₁.isoIsPullback_hom_snd _ _ H₂
  refine basis_transport hw D.P.isLB D'.P.isLB θ _ _ θ₂ _ (fun i => (snd T₂ D'.P.A).left ≫ D'.famφB α' i)
    (fun i => by rw [Category.assoc, hφ, ← θ₁]; simp only [Category.assoc]) _ b'
    (fun i => DVR.pullSec _ _ _ (b₀ i) (snd T₂ D'.P.A).left)
    (fun i => (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (f (t i))) (fun i => (hf _ (ht i)).map _)
    (fun i Z r z j q hj hq => ?_) (hb₀ R' g _ fun i j => rfl)
  have mj : (r ≫ (snd T₁ D.P.A).left) z ∈ LB.wchart D.P.L (D.famφB (hD.xe α')) j :=
    wchart_comp_le _ _ (snd T₁ D.P.A).left j hj
  have mq : ((r ≫ θ.hom) ≫ (snd T₂ D'.P.A).left) z ∈ LB.wchart D'.P.L (D'.famφB α') q :=
    wchart_comp_le _ _ (snd T₂ D'.P.A).left q hq
  have er : ((r ≫ θ.hom) ≫ (snd T₂ D'.P.A).left) ≫ F = r ≫ (snd T₁ D.P.A).left := by
    rw [← θ₁]; simp only [Category.assoc]
  have mj' : ((r ≫ θ.hom) ≫ (snd T₂ D'.P.A).left) z ∈
      LB.wchart D.P.L (fun κ => F ≫ D.famφB (hD.xe α') κ) j := Set.mem_iInter.2 fun κ => by
    show ((((r ≫ θ.hom) ≫ (snd T₂ D'.P.A).left) ≫ F) ≫ D.famφB (hD.xe α') κ) z ∈ D.P.L.U (j κ)
    rw [er]; exact Set.mem_iInter.1 mj κ
  have e₁ := hb i Z _ z j mj'
  rw [er, ha i Z _ z j q mj' mq] at e₁
  refine (congrArg (gs r z _) (hb' i j)).trans ((gs_res r z _ hj _).trans ((gs_pull r _ z _ mj _).trans
    (e₁.trans (congrArg₂ (· * ·) ?_ (congrArg₂ (· * ·) ?_ ?_)))))
  · rw [← Category.assoc, er, Category.assoc, H₁.w, ← Category.assoc, gc, ← gs_pull _ _ z ⊤ trivial]
    exact congrArg (gs _ z ⊤) congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)).hom (t i)).symm
  · simp only [pw, Category.assoc]
  · exact ((gs_res _ z _ hq _).trans (gs_pull _ _ z _ mq _)).symm
end GlobalTheory.TwistLoc

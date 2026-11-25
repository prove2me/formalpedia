-- Prove2me | solution 1 for GlobalTheory.EndDivisible.eq_one_of_forall_pow_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:51:20.128846+00:00
-- url     : https://prove2.me/submissions/f27997ac-fbf9-4e7f-a89a-a302a5bba52f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfLocalOnBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeOfSumEqZero
import Theorems.Thm_GlobalTheory_EndDivisible_germPull_apply
import Theorems.Thm_GlobalTheory_EndDivisible_gs_appLE
import Theorems.Thm_GlobalTheory_EndDivisible_exists_factor
import Theorems.Thm_GlobalTheory_EndDivisible_exists_monomials
import Theorems.Thm_GlobalTheory_EndDivisible_mem_range_of_sum_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_linComb_isLB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SectionArithmetic_isUnit_sval


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.EndDivisible
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic TopologicalSpace
namespace GlobalTheory.EndDivisible
theorem _root_.solution :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f) → (∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ), ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (mulA P.A n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (M : LB P.A.left), M.IsLB → ∃ n : ℕ, ∀ s : Fin n → LB.Sec M, ∃ c : Fin n → Γ(Spec (CommRingCat.of K), ⊤), c ≠ 0 ∧ ∀ i, ∑ k, (P.A.hom.appLE ⊤ (M.U i) le_top).hom (c k) * (s k).f i = 0) → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (q : ℕ), 2 ≤ q → ∀ u : P.A ⟶ P.A, (∀ k : ℕ, ∃ ψ : P.A ⟶ P.A, IsMonHom ψ ∧ u = ψ ^ (q ^ k)) → u = 1 := by
  intro hGI hmul hfin K _ _ P q hq u hu
  have := P.isAb.proper
  have : GeometricallyIntegral P.A.hom := hGI _ _ _ P.isAb.smooth P.isAb.geomConnected
  have : IsIntegral P.A.left := GeometricallyIntegral.isIntegral_of_subsingleton P.A.hom
  have : P.A.left.IsSeparated := ⟨by
    rw [← terminal.comp_from P.A.hom]; infer_instance⟩
  let E := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  have hk : IsField Γ(Spec (CommRingCat.of K), ⊤) := E.toMulEquiv.isField (Field.toIsField K)
  obtain ⟨N, -, M, s, hcov, hs⟩ := P.ample ⊤ (isAffineOpen_top _)
  obtain ⟨n, hn⟩ := hfin K P _ (DVR.linComb_isLB P.L P.isLB (K := Unit) (fun _ => u.left) (fun _ => (N : ℤ)))
  obtain ⟨ψ, hψ, hu⟩ := hu n
  have H := hmul _ P (q ^ n)
  rw [← Nat.cast_pow] at H
  obtain ⟨α, hα⟩ := H
  have hnt : n ≤ (q ^ n) ^ 2 := (Nat.lt_pow_self hq).le.trans (Nat.le_self_pow two_ne_zero _)
  let w := (P.A.hom ⁻¹ᵁ ⊤).ι
  let f : P.A.left ⟶ (P.A.hom ⁻¹ᵁ ⊤).toScheme := IsOpenImmersion.lift w ψ.left (by
    rintro _ -
    rw [Scheme.Opens.range_ι]
    trivial)
  have hf : f ≫ w = ψ.left := IsOpenImmersion.lift_fac _ _ _
  have hu' : u.left = f ≫ w ≫ (mulA P.A (q ^ n)).left := by
    rw [← Category.assoc, hf, ← Over.comp_left, mulA, MonObj.comp_pow, Category.comp_id, hu]
  obtain ⟨z⟩ : Nonempty P.A.left := inferInstance
  obtain ⟨i, hi⟩ : ∃ i, f z ∈ nonzeroLocus (s i) := Opens.mem_iSup.1 (by rw [hcov]; trivial)
  obtain ⟨hD, r, hr, hsurj⟩ := hs i
  obtain ⟨J, hJ⟩ : ∃ J, Good P.L z J := by
    choose I hI using fun χ : P.A.left ⟶ P.A.left => exists_chart P.isLB (χ z)
    exact ⟨I, hI⟩
  let κ := germPull P.A.hom z ⊤ trivial
  let ρ := germPull f z _ hi
  have hy : IsUnit (sval (s i) f z J) := by
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hi
    exact isUnit_sval (s i) f z hJ k hk
  have hrj : ∀ j, ρ (r j) ∈ κ.range := fun j => by
    have e : sval (s j) f z J = ρ (r j) * sval (s i) f z J := by
      have hm := hJ.mem (K := Fin N) (fun _ => w) f
      have hm' : f z ∈ nonzeroLocus (s i) ⊓ (powOver P.A P.L ⊤ N).U (fun _ => J (f ≫ w)) := ⟨hi, hm⟩
      have := congrArg (gs f z _) (hr j (fun _ => J (f ≫ w)))
      rw [gs_mul f z _ hm', gs_res f z _ hm', gs_res f z _ hm', gs_res f z _ hm'] at this
      rw [germPull_apply]
      exact this
    obtain ⟨b, hb⟩ := exists_monomials P.L P.isLB w N (s i) (s j) _ _ α hα f u.left hu' z J hJ
    choose σ hσ using fun a : Fin n => hb a (a.2.le.trans hnt)
    obtain ⟨c, hc, h0⟩ := hn σ
    have hm := hJ.mem (K := Unit) (fun _ => u.left) (𝟙 _)
    have h1 := (map_sum _ _ _).symm.trans
      ((congrArg (germPull (𝟙 _) z _ hm) (h0 (fun _ => J (𝟙 _ ≫ u.left)))).trans (map_zero _))
    have h2 : (∑ k : Fin n, (κ.comp E.symm.toRingHom) (E (c k)) * ρ (r j) ^ (k : ℕ)) *
        (sval (s i) f z J ^ ((q ^ n) ^ 2) * b.val) = 0 := by
      rw [Finset.sum_mul, ← h1]
      refine Finset.sum_congr rfl fun k _ => ?_
      refine Eq.trans ?_ ((germPull_apply (𝟙 _) z _ hm _).trans (gs_mul (𝟙 _) z _ hm _ _)).symm
      refine Eq.trans ?_ (congrArg₂ (· * ·) (gs_appLE (𝟙 _) P.A.hom z ⊤ _ le_top hm (c k)) (hσ k)).symm
      have e₁ : (κ.comp E.symm.toRingHom) (E (c k)) = gs (𝟙 _ ≫ P.A.hom) z ⊤ (c k) := by
        rw [Category.id_comp]
        exact (congrArg κ (E.symm_apply_apply _)).trans (germPull_apply _ _ _ _ _)
      rw [e₁, e, mul_pow]
      conv_lhs => rw [← Nat.add_sub_of_le (k.2.le.trans hnt), pow_add]
      ring
    obtain ⟨a, ha⟩ := mem_range_of_sum_eq_zero (κ.comp E.symm.toRingHom) (fun k => E (c k))
      (fun h => hc (funext fun k => E.injective ((congrFun h k).trans (map_zero E).symm))) (ρ (r j))
      ((mul_eq_zero.1 h2).resolve_right ((hy.pow _).mul b.isUnit).ne_zero)
    exact ⟨_, ha⟩
  have hall : ∀ a, ρ a ∈ κ.range := fun a => by
    obtain ⟨p, rfl⟩ := hsurj a
    induction p using MvPolynomial.induction_on with
    | C c =>
      rw [MvPolynomial.eval₂Hom_C]
      obtain ⟨c', rfl⟩ : ∃ c', ((⊤ : (Spec (CommRingCat.of K)).Opens).ι.appTop).hom c' = c :=
        have : IsIso (⊤ : (Spec (CommRingCat.of K)).Opens).ι :=
          inferInstanceAs (IsIso (Spec (CommRingCat.of K)).topIso.hom)
        (ConcreteCategory.bijective_of_isIso ((⊤ : (Spec (CommRingCat.of K)).Opens).ι.app ⊤)).2 c
      refine ⟨c', ?_⟩
      refine (germPull_apply _ _ _ _ _).trans (Eq.trans ?_ (germPull_apply _ _ _ _ _).symm)
      refine Eq.symm ((gs_appLE f _ z ⊤ _ le_top hi _).trans
        ((gs_pull _ (⊤ : (Spec (CommRingCat.of K)).Opens).ι z ⊤ trivial c').trans ?_))
      rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hf, Over.w]
    | add p p' h h' => rw [map_add, map_add]; exact add_mem h h'
    | mul_X p j h => rw [map_mul, map_mul, MvPolynomial.eval₂Hom_X']; exact mul_mem h (hrj j)
  obtain ⟨p, hp⟩ := exists_factor f w P.A.hom hk _ hD z hi (fun a => by
    obtain ⟨c, hc⟩ := hall a
    exact ⟨c, (germPull_apply _ _ _ _ _).symm.trans (hc.trans (germPull_apply _ _ _ _ _))⟩)
  rw [hf] at hp
  have h1 : η[P.A].left ≫ P.A.hom = 𝟙 _ := Over.w η[P.A]
  have h2 : η[P.A].left = p := by
    have := congrArg (fun x => x.left) (IsMonHom.one_hom ψ)
    simp only [Over.comp_left] at this
    rw [← this, hp, ← Category.assoc, h1]
    exact Category.id_comp _
  have h3 : ψ = 1 := by
    apply Over.OverMorphism.ext
    rw [hp, ← h2, Hom.one_def]
    simp
  rw [hu, h3, one_pow]
end GlobalTheory.EndDivisible

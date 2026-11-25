-- Prove2me | solution 1 for GlobalTheory.ThetaAmple.relAmple_of_values
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:45:59.059511+00:00
-- url     : https://prove2.me/submissions/768f9eb4-22b2-497c-ad37-b489f2af3418

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_RelAmpleThetaBundleProjectiveModel
import Theorems.Thm_GlobalTheory_ThetaAmple_opens_le_of_points
import Theorems.Thm_GlobalTheory_ThetaAmple_top_le_preimage_iSup
import Theorems.Thm_GlobalTheory_ThetaAmple_top_le_preimage_wchart
import Theorems.Thm_P2M_GlobalTheory_ThetaAmple_valAt__linComb_g_c2c02d34e6d0
import Theorems.Thm_GlobalTheory_ThetaAmple_relAmple_of_top
import Theorems.Thm_GlobalTheory_ComplexPoints_top_le_preimage_basicOpen_iff
import Theorems.Thm_GlobalTheory_top_le_preimage_basicOpen_iff
import Theorems.Thm_GlobalTheory_top_le_preimage_comp
import Theorems.Thm_GlobalTheory_top_le_preimage_inf
import Theorems.Thm_P2M_GlobalTheory_top_le_preimage_of_valAt__ne_zero_a6acb076de42
import Theorems.Thm_P2M_GlobalTheory_valAt__appLE_1af07a5a9e22
import Theorems.Thm_P2M_GlobalTheory_valAt__map_238ef0722272
import Theorems.Thm_P2M_GlobalTheory_valAt__mul_dca2439ccec2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaAmple
namespace GlobalTheory.ThetaAmple
theorem _root_.solution
    (hext : ∀ (X : Over (Sp ℂ)), IsReduced X.left → LocallyOfFiniteType X.hom → ∀ (U : X.left.Opens)
      (f f' : Γ(X.left, U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U →
        valAt' x.left U f = valAt' x.left U f') → f = f')
    {X : Over (Sp ℂ)} [IsReduced X.left] [LocallyOfFiniteType X.hom] {L : LB X.left} (hL : L.IsLB)
    {Z κ : Type} [Fintype κ] [Nonempty κ] (ex : Z → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (hex : Function.Surjective ex)
    (fr : L.ι → Z → ℂ) (fr_ne : ∀ i z, ⊤ ≤ (ex z).left ⁻¹ᵁ L.U i → fr i z ≠ 0)
    (fr_compat : ∀ i j z, ⊤ ≤ (ex z).left ⁻¹ᵁ (L.U i ⊓ L.U j) →
      fr i z = valAt' (ex z).left (L.U i ⊓ L.U j) (L.g i j).val * fr j z)
    (f : κ → Z → ℂ) {N : ℕ} (hN : 1 ≤ N)
    (hsec : ∀ c (j : Fin N → L.ι), ∃ (U : X.left.Opens) (φ : Γ(X.left, U)), ∀ z,
      (∀ k, ⊤ ≤ (ex z).left ⁻¹ᵁ L.U (j k)) →
        ⊤ ≤ (ex z).left ⁻¹ᵁ U ∧ valAt' (ex z).left U φ = f c z * ∏ k, fr (j k) z)
    (D : κ → X.left.Opens) (hcov : ⨆ c, D c = ⊤) (haff : ∀ c, IsAffineOpen (D c))
    (hD : ∀ c z, ⊤ ≤ (ex z).left ⁻¹ᵁ D c ↔ f c z ≠ 0) (r : ∀ c, κ → Γ(X.left, D c))
    (hr : ∀ c c' z, f c z ≠ 0 → valAt' (ex z).left (D c) (r c c') = f c' z / f c z)
    (hgen : ∀ c (t : Γ(X.left, D c)), ∃ F : MvPolynomial κ ℂ, t = MvPolynomial.eval₂
      (RingHom.comp (X.hom.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) (r c) F) :
    Out.RelAmple X L := by
  apply relAmple_of_top
  obtain ⟨M, ⟨e⟩⟩ : ∃ M : ℕ, Nonempty (Fin (M + 1) ≃ κ) :=
    ⟨Fintype.card κ - 1, ⟨(finCongr (Nat.sub_add_cancel Fintype.card_pos)).trans (Fintype.equivFin κ).symm⟩⟩
  let ψ : (X.hom ⁻¹ᵁ ⊤).toScheme ⟶ X.left := (X.hom ⁻¹ᵁ ⊤).ι
  have hiso : IsIso ψ := inferInstanceAs (IsIso X.left.topIso.hom)
  have hpt : ∀ x : Sp ℂ ⟶ (X.hom ⁻¹ᵁ ⊤).toScheme, x ≫ ψ ≫ X.hom = 𝟙 _ → ∃ z, x ≫ ψ = (ex z).left := by
    intro x hx
    obtain ⟨z, hz⟩ := hex (Over.homMk (x ≫ ψ) ((Category.assoc _ _ _).trans hx))
    exact ⟨z, by rw [hz]; rfl⟩
  have ext : ∀ (U : (X.hom ⁻¹ᵁ ⊤).toScheme.Opens) (a b : Γ((X.hom ⁻¹ᵁ ⊤).toScheme, U)),
      (∀ (x : Sp ℂ ⟶ (X.hom ⁻¹ᵁ ⊤).toScheme) z, x ≫ ψ = (ex z).left → ⊤ ≤ x ⁻¹ᵁ U →
        valAt' x U a = valAt' x U b) → a = b := by
    intro U a b h
    refine hext (Over.mk (ψ ≫ X.hom)) (inferInstanceAs (IsReduced (X.hom ⁻¹ᵁ ⊤).toScheme))
      (inferInstanceAs (LocallyOfFiniteType (ψ ≫ X.hom))) U a b fun x hx => ?_
    obtain ⟨z, hz⟩ := hpt x.left (Over.w x)
    exact h x.left z hz hx
  have le : ∀ (U V : (X.hom ⁻¹ᵁ ⊤).toScheme.Opens),
      (∀ (x : Sp ℂ ⟶ (X.hom ⁻¹ᵁ ⊤).toScheme) z, x ≫ ψ = (ex z).left → ⊤ ≤ x ⁻¹ᵁ U → ⊤ ≤ x ⁻¹ᵁ V) → U ≤ V := by
    intro U V h
    refine opens_le_of_points (ψ ≫ X.hom) fun x hx => ?_
    obtain ⟨z, hz⟩ := hpt x hx
    exact h x z hz
  have hch : ∀ (x : Sp ℂ ⟶ (X.hom ⁻¹ᵁ ⊤).toScheme) z, x ≫ ψ = (ex z).left → ∀ j : Fin N → L.ι,
      (⊤ ≤ x ⁻¹ᵁ (Out.powOver X L ⊤ N).U j ↔ ∀ k, ⊤ ≤ (ex z).left ⁻¹ᵁ L.U (j k)) := by
    intro x z hz j
    rw [← hz]
    exact top_le_preimage_wchart L ψ j x
  choose U φ hφ using hsec
  have hU : ∀ c j, (Out.powOver X L ⊤ N).U j ≤ ψ ⁻¹ᵁ U c j := fun c j => le _ _ fun x z hz hx => by
    rw [← top_le_preimage_comp, hz]
    exact (hφ c j z ((hch x z hz j).1 hx)).1
  have hv : ∀ c j (x : Sp ℂ ⟶ (X.hom ⁻¹ᵁ ⊤).toScheme) z, x ≫ ψ = (ex z).left →
      ⊤ ≤ x ⁻¹ᵁ (Out.powOver X L ⊤ N).U j →
      valAt' x _ ((ψ.appLE _ _ (hU c j)).hom (φ c j)) = f c z * ∏ k, fr (j k) z := fun c j x z hz hx => by
    rw [valAt'_appLE x ψ _ _ _ _ hx, hz]
    exact (hφ c j z ((hch x z hz j).1 hx)).2
  let s : κ → LB.Sec (Out.powOver X L ⊤ N) := fun c =>
    ⟨fun j => (ψ.appLE _ _ (hU c j)).hom (φ c j), fun j j' => ext _ _ _ fun x z hz hx => by
      have hx' := (top_le_preimage_inf x _ _).1 hx
      rw [valAt'_mul, valAt'_map x _ _ hx, valAt'_map x _ _ hx, hv c j x z hz hx'.1, hv c j' x z hz hx'.2]
      refine Eq.trans ?_ (congrArg (· * _) (valAt'_linComb_g L ψ j j' x hx).symm)
      rw [hz, mul_left_comm, ← Finset.prod_mul_distrib]
      refine congrArg _ (Finset.prod_congr rfl fun k _ => fr_compat _ _ z ?_)
      exact (top_le_preimage_inf _ _ _).2 ⟨(hch x z hz j).1 hx'.1 k, (hch x z hz j').1 hx'.2 k⟩⟩
  have hnz : ∀ c (x : Sp ℂ ⟶ (X.hom ⁻¹ᵁ ⊤).toScheme) z, x ≫ ψ = (ex z).left →
      (⊤ ≤ x ⁻¹ᵁ Out.nonzeroLocus (s c) ↔ f c z ≠ 0) := by
    intro c x z hz
    refine (top_le_preimage_iSup x _).trans ⟨fun ⟨j, hj⟩ => ?_, fun h => ?_⟩
    · have h1 := (top_le_preimage_basicOpen_iff x _ _).1 hj
      have h2 := hv c j x z hz (top_le_preimage_of_valAt'_ne_zero x h1)
      exact left_ne_zero_of_mul (h2 ▸ h1)
    · obtain ⟨i, hi⟩ := (top_le_preimage_iSup (ex z).left L.U).1 (by rw [hL.cover]; exact le_top)
      refine ⟨fun _ => i, (top_le_preimage_basicOpen_iff x _ _).2 ?_⟩
      refine (hv c (fun _ => i) x z hz ((hch x z hz _).2 fun _ => hi)).trans_ne ?_
      exact mul_ne_zero h (Finset.prod_ne_zero_iff.2 fun _ _ => fr_ne i z hi)
  have loc : ∀ c, Out.nonzeroLocus (s c) = ψ ⁻¹ᵁ D c := fun c => by
    refine le_antisymm (le _ _ fun x z hz hx => ?_) (le _ _ fun x z hz hx => ?_)
    · rw [← top_le_preimage_comp, hz]
      exact (hD c z).2 ((hnz c x z hz).1 hx)
    · rw [← top_le_preimage_comp, hz] at hx
      exact (hnz c x z hz).2 ((hD c z).1 hx)
  refine ⟨N, hN, M, fun i => s (e i), ?_, fun i => ⟨?_, fun j => (ψ.appLE _ _ (loc (e i)).le).hom (r (e i) (e j)),
    fun j k => ext _ _ _ fun x z hz hx => ?_, ?_⟩⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.1 (show ψ y ∈ ⨆ c, D c by rw [hcov]; trivial)
    obtain ⟨i, rfl⟩ := e.surjective c
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, by rw [loc]; exact hc⟩
  · rw [loc]; exact (haff _).preimage ψ
  · have hx' := (top_le_preimage_inf x _ _).1 hx
    have h0 := (hnz _ x z hz).1 hx'.1
    rw [valAt'_mul, valAt'_map x _ _ hx, valAt'_map x _ _ hx, valAt'_map x _ _ hx, valAt'_appLE x ψ _ _ _ _ hx'.1, hz,
      hr _ _ z h0]
    refine (hv _ k x z hz hx'.2).trans (Eq.trans ?_ (congrArg (_ * ·) (hv _ k x z hz hx'.2).symm))
    field_simp
  · have hap : IsIso (ψ.appLE _ _ (loc (e i)).le) := by
      have key : ∀ V (h : V = ψ ⁻¹ᵁ D (e i)), IsIso (ψ.appLE _ V h.le) := by
        rintro _ rfl
        rw [Scheme.Hom.appLE_eq_app]
        infer_instance
      exact key _ (loc _)
    let θ : CommRingCat.of ℂ ⟶ Γ((⊤ : (Sp ℂ).Opens).toScheme, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ (⊤ : (Sp ℂ).Opens).ι.appLE ⊤ ⊤ le_top
    have hc : (ψ.appLE _ _ (loc (e i)).le).hom.comp (RingHom.comp (X.hom.appLE ⊤ _ le_top).hom
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) =
        ((X.hom ∣_ ⊤).appLE ⊤ (Out.nonzeroLocus (s (e i))) le_top).hom.comp θ.hom := by
      have e₁ := Scheme.Hom.appLE_comp_appLE ψ X.hom ⊤ (D (e i)) _ le_top (loc (e i)).le
      have e₂ := Scheme.Hom.appLE_comp_appLE (X.hom ∣_ ⊤) (⊤ : (Sp ℂ).Opens).ι ⊤ ⊤
        (Out.nonzeroLocus (s (e i))) le_top le_top
      have e₃ : ∀ (a b : (X.hom ⁻¹ᵁ ⊤).toScheme ⟶ Sp ℂ), a = b →
          a.appLE ⊤ (Out.nonzeroLocus (s (e i))) le_top = b.appLE ⊤ (Out.nonzeroLocus (s (e i))) le_top := by
        rintro _ _ rfl; rfl
      have e₄ := e₁.trans ((e₃ _ _ (morphismRestrict_ι X.hom ⊤).symm).trans e₂.symm)
      ext a
      exact congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) e₄
    intro d
    obtain ⟨d, rfl⟩ := (ConcreteCategory.bijective_of_isIso (ψ.appLE _ _ (loc (e i)).le)).2 d
    obtain ⟨F, rfl⟩ := hgen _ d
    refine ⟨MvPolynomial.map θ.hom (MvPolynomial.rename e.symm F), ?_⟩
    rw [MvPolynomial.eval₂Hom_map_hom, ← hc, MvPolynomial.eval₂Hom_rename]
    refine Eq.trans ?_ (MvPolynomial.map_eval₂Hom _ (r (e i)) (ψ.appLE _ _ (loc (e i)).le).hom F).symm
    congr 2
    funext c
    simp
end GlobalTheory.ThetaAmple

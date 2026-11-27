-- Prove2me | solution 1 for GlobalTheory.polarised_lattice_eighth_power
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:40:53.739215+00:00
-- url     : https://prove2.me/submissions/53d5d207-dea3-4073-a265-e0030f6f716e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_UnimodularSymplecticCoordinatesAndLatticeRank
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSiegelForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsEquivPiRangeOfMatrixUnits
import Theorems.Thm_GlobalTheory_exists_equiv_pi_range_of_matrixUnits
import Theorems.Thm_GlobalTheory_matrixUnits_apply
import Theorems.Thm_GlobalTheory_hermForm_pullback
import Theorems.Thm_GlobalTheory_exists_form_range_matrixUnit
import Theorems.Thm_GlobalTheory_IsSymplecticBasisOfType_finrank_eq
import Theorems.Thm_GlobalTheory_SiegelPeriod_exists_siegel_form
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_GlobalTheory_unimodular_symplectic_coordinates_and_lattice_rank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (h g : ℕ) (G : Matrix (Fin 8) (Fin 8) ℤ) (σ : Fin 8 × Fin h ≃ Fin g) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (r : Matrix (Fin 8) (Fin 8) ℤ →+* Module.End ℤ La), G.IsSymm → (G.map (Int.cast : ℤ → ℝ)).PosDef → G.det = 1 → Function.Bijective EF → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → (∀ a, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ x, F (Q x) = Q (r a x)) → (∀ a a', a.transpose * G = G * a' → ∀ x y, EF (r a x) y = EF x (r a' y)) → ∃ (τ : Matrix (Fin h) (Fin h) ℂ) (e : La ≃+ (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (hh : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (τ).IsSymm ∧ ((τ).map Complex.im).PosDef ∧ (∀ x u i, hh (Q x) (σ (u, i)) = τ.mulVec (fun i' => (e x u (.inl i') : ℂ)) i + (e x u (.inr i) : ℂ)) ∧ (∀ x y, EF x y = ∑ u, ∑ v, G u v * omegaStd (e x u) (e y v)) ∧ ∀ a x u, e (r a x) u = ∑ v, a u v • e x v := by
  intro h g G σ La _ EF Q Hm r _ hpos hdet hb hQ hF hadj
  obtain ⟨hfree, hfin, hrk, halt⟩ :=
    unimodular_symplectic_coordinates_and_lattice_rank.2 La EF g Q Hm hQ
  obtain ⟨hinj, hdisc, hspan, hherm, hHpos, hIm⟩ := hQ
  have hg : g = 8 * h := by simpa using (Fintype.card_congr σ).symm
  have hG : (0 : ℤ) < G 0 0 := by
    have := hpos.diag_pos (i := 0)
    simpa using this
  obtain ⟨φ, E, hφ, hEb, hEalt, hsum, h00⟩ :=
    exists_form_range_matrixUnit G EF r hG.ne' hdet hb halt hadj
  have hrk0 : Module.finrank ℤ (LinearMap.range (r (Matrix.single 0 0 1))) = 2 * h := by
    have := φ.finrank_eq
    rw [hrk, Module.finrank_pi_fintype] at this
    simp at this
    omega
  obtain ⟨bas, hbas⟩ := unimodular_symplectic_coordinates_and_lattice_rank.1 _ E h hEb hEalt hrk0
  choose F hF using hF
  have hspanC : Submodule.span ℂ (Set.range Q) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    exact Submodule.span_subset_span ℝ ℂ _ (hspan ▸ Submodule.mem_top)
  obtain ⟨h1, h2, h3⟩ := matrixUnits_apply r
  obtain ⟨ψ, hψ, -⟩ := exists_equiv_pi_range_of_matrixUnits (fun u => F (Matrix.single 0 u 1))
    (fun u => F (Matrix.single u 0 1)) (F (Matrix.single 0 0 1))
    (fun u v => by
      have : F (Matrix.single 0 u 1) ∘ₗ F (Matrix.single v 0 1) =
          if u = v then F (Matrix.single 0 0 1) else 0 := by
        refine LinearMap.ext_on_range hspanC fun x => ?_
        simp only [LinearMap.comp_apply, hF, h1]
        split_ifs <;> simp [hF]
      intro x
      have := LinearMap.congr_fun this x
      rw [LinearMap.comp_apply] at this
      rw [this]; split_ifs <;> simp)
    (fun z => by
      have : ∑ u, F (Matrix.single u 0 1) ∘ₗ F (Matrix.single 0 u 1) = LinearMap.id := by
        refine LinearMap.ext_on_range hspanC fun x => ?_
        simp only [LinearMap.sum_apply, LinearMap.comp_apply, hF, ← map_sum, h2, LinearMap.id_apply]
      simpa using LinearMap.congr_fun this z)
    (fun z => by
      have : F (Matrix.single 0 0 1) ∘ₗ F (Matrix.single 0 0 1) = F (Matrix.single 0 0 1) := by
        refine LinearMap.ext_on_range hspanC fun x => ?_
        simp only [LinearMap.comp_apply, hF, h3]
      exact LinearMap.congr_fun this z)
  have hdim : Module.finrank ℂ (Fin h → ℂ) =
      Module.finrank ℂ (LinearMap.range (F (Matrix.single 0 0 1))) := by
    have := ψ.finrank_eq
    rw [Module.finrank_pi_fintype, Module.finrank_pi_fintype] at this
    simp at this
    simp
    omega
  let j := LinearEquiv.ofFinrankEq _ _ hdim
  let T : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ) :=
    j.symm.toLinearMap ∘ₗ (F (Matrix.single 0 0 1)).rangeRestrict
  let Jl : (Fin h → ℂ) →ₗ[ℂ] (Fin g → ℂ) := Submodule.subtype _ ∘ₗ j.toLinearMap
  have hJT : ∀ z, Jl (T z) = F (Matrix.single 0 0 1) z := fun z => by simp [Jl, T]
  have hJinj : Function.Injective Jl := Subtype.val_injective.comp j.injective
  have hTs : Function.Surjective T :=
    j.symm.surjective.comp (F (Matrix.single 0 0 1)).surjective_rangeRestrict
  let Q₀ : LinearMap.range (r (Matrix.single 0 0 1)) →+ (Fin h → ℂ) :=
    T.toAddMonoidHom.comp (Q.comp (Submodule.subtype _).toAddMonoidHom)
  have hQ₀ : ∀ x, Jl (Q₀ x) = Q x := by
    rintro ⟨_, z, rfl⟩
    change Jl (T (Q _)) = _
    rw [hJT, hF]
    exact congrArg Q (h3 z)
  let J := LinearMap.toMatrix' Jl
  have hJ : ∀ z, J.mulVec z = Jl z := fun z => LinearMap.toMatrix'_mulVec _ _
  have hGR : (0 : ℝ) < G 0 0 := by exact_mod_cast hG
  obtain ⟨m, τ, hm, -, -, hτs, hτp, -, hτ⟩ := GlobalTheory.SiegelPeriod.exists_siegel_form _ E h bas Q₀
    ((((G 0 0 : ℝ)⁻¹ : ℝ) : ℂ) • (J.transpose * Hm * J.map star)) hbas
    ⟨fun x y hxy => Subtype.ext (hinj (by rw [← hQ₀, ← hQ₀, hxy])),
      by
        let f : Q₀.range → Q.range := fun z => ⟨Jl z, by
          obtain ⟨x, hx⟩ := z.2
          exact ⟨x, by rw [← hx, hQ₀]⟩⟩
        exact DiscreteTopology.of_continuous_injective (f := f)
          ((Jl.continuous_of_finiteDimensional.comp continuous_subtype_val).subtype_mk _)
          fun a b hab => Subtype.ext (hJinj (congrArg (fun z : Q.range => (z : Fin g → ℂ)) hab)),
      by
        rw [eq_top_iff]
        intro z _
        obtain ⟨w, rfl⟩ := hTs z
        have hw : w ∈ Submodule.span ℝ (Set.range Q) := hspan ▸ Submodule.mem_top
        refine Submodule.span_mono ?_
          (Submodule.apply_mem_span_image_of_mem_span (T.restrictScalars ℝ) hw)
        rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
        refine ⟨⟨_, x, rfl⟩, hJinj ?_⟩
        rw [hQ₀, LinearMap.restrictScalars_apply, hJT, hF],
      by
        have e1 : J.map star = J.transpose.conjTranspose := by ext; simp
        rw [e1]
        have := Matrix.isHermitian_mul_mul_conjTranspose J.transpose hherm
        unfold Matrix.IsHermitian at this ⊢
        rw [Matrix.conjTranspose_smul, this]; simp,
      fun z hz => by
        rw [hermForm_pullback, Complex.re_ofReal_mul, hJ]
        exact mul_pos (inv_pos.2 hGR) (hHpos _ fun h0 => hz (hJinj (by rw [h0, map_zero]))),
      fun x y => by
        rw [hermForm_pullback, Complex.im_ofReal_mul, hJ, hJ, hQ₀, hQ₀, hIm, h00]
        push_cast
        field_simp⟩
  let mE : (Fin h → ℂ) ≃ₗ[ℂ] (Fin h → ℂ) := Matrix.toLinearEquiv' m hm.invertible
  have hmE : ∀ z, mE z = m.mulVec z := fun _ => rfl
  let e : La ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)) :=
    φ ≪≫ₗ LinearEquiv.piCongrRight fun _ => bas.symm
  have he : ∀ x u, e x u = bas.symm (φ x u) := fun _ _ => rfl
  let hh : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) :=
    ψ ≪≫ₗ (LinearEquiv.piCongrRight fun _ => j.symm ≪≫ₗ mE) ≪≫ₗ
      (LinearEquiv.curry ℂ ℂ (Fin 8) (Fin h)).symm ≪≫ₗ LinearEquiv.funCongrLeft ℂ ℂ σ.symm
  have hhh : ∀ z u i, hh z (σ (u, i)) = m.mulVec (j.symm (ψ z u)) i := fun z u i => by
    simp [hh, hmE]
  refine ⟨τ, e.toAddEquiv, hh, hτs, hτp, fun x u i => ?_, fun x y => ?_, fun a x u => ?_⟩
  · have e1 : j.symm (ψ (Q x) u) = Q₀ (bas (e x u)) := by
      apply hJinj
      rw [hQ₀, he, LinearEquiv.apply_symm_apply, hφ, ← hF, ← hψ]
      simp [Jl]
    rw [hhh, e1, hτ]
    rfl
  · rw [hsum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    change G u v * E (φ x u) (φ y v) = G u v * omegaStd (bas.symm (φ x u)) (bas.symm (φ y v))
    rw [← hbas, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  · change bas.symm (φ (r a x) u) = ∑ v, a u v • bas.symm (φ x v)
    simp only [← map_smul, ← map_sum]
    refine congrArg bas.symm (Subtype.ext ?_)
    have : Matrix.single (0 : Fin 8) u (1 : ℤ) * a = ∑ v, a u v • Matrix.single (0 : Fin 8) v (1 : ℤ) := by
      ext i k
      by_cases hi : i = 0
      · subst hi; simp [Matrix.sum_apply, Matrix.single_apply]
      · simp [Matrix.sum_apply, Matrix.single_apply, hi, Ne.symm hi]
    rw [hφ, ← Module.End.mul_apply, ← map_mul, this, map_sum, LinearMap.sum_apply,
      Submodule.coe_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [map_zsmul, LinearMap.smul_apply, Submodule.coe_smul, hφ]
end GlobalTheory

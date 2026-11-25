-- Prove2me | solution 1 for GlobalTheory.KS.Endo.comm_of_endo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:50:48.178363+00:00
-- url     : https://prove2.me/submissions/feaf8dbb-163f-4ee4-b0ca-31b49ce5b0fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EntireAntilinearLatticePeriodsConstStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueUniformisingVectorVerticalTangentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDifferentiableOnVerticalVectorFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KodairaSpencerCommutesWithEndomorphism
import Theorems.Thm_GlobalTheory_KS_Endo_ptDer_push
import Theorems.Thm_GlobalTheory_KS_Endo_ptDer_sub
import Theorems.Thm_GlobalTheory_KS_Endo_app_top_constFn
import Theorems.Thm_GlobalTheory_KS_Endo_ex_add_lattice
import Theorems.Thm_GlobalTheory_KS_Endo_fn_differentiableAt
import Theorems.Thm_GlobalTheory_KS_Endo_fderiv_fn_add_lattice
import Theorems.Thm_GlobalTheory_T_entire_antilinear_lattice_periods_const
import Theorems.Thm_GlobalTheory_T_existsUnique_uniformising_vector_vertical_tangent
import Theorems.Thm_GlobalTheory_T_exists_differentiableOn_verticalVectorField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.Endo
private theorem valAt'_comp_lemma {Y Z : Scheme.{0}} (x : Sp ℂ ⟶ Y) (φ : Y ⟶ Z) (U : Z.Opens) (a : Γ(Z, U)) :
    valAt' (x ≫ φ) U a = valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom a) := by
  unfold valAt'
  by_cases h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U
  · have h' : ⊤ ≤ x ⁻¹ᵁ φ ⁻¹ᵁ U := h
    rw [dif_pos h, dif_pos h']
    unfold valAt
    rw [Scheme.Hom.comp_appLE]
    rfl
  · have h' : ¬ ⊤ ≤ x ⁻¹ᵁ φ ⁻¹ᵁ U := h
    rw [dif_neg h, dif_neg h']
variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g) {X : Scheme.{0}}
end GlobalTheory.KS.Endo
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Endo
variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g) {X : Scheme.{0}}
namespace GlobalTheory.KS.Endo
theorem _root_.solution : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D Θ s, KSRel u p m D Θ s → ∀ (f : X ⟶ X) (f₀ : P₀.A ⟶ P₀.A) (F : (Fin P₀.g → ℂ) →ₗ[ℂ] (Fin P₀.g → ℂ)), f ≫ p = p → f₀.left ≫ m = m ≫ f → (∀ z, u.ex (F z) = u.ex z ≫ f₀) → Comm Θ F := by
  intro P₀ u Hm χ hU R instR x₀ X p m hp hpb D Θ s hKS f f₀ F hfp hf₀ hF
  have hFdiff : Differentiable ℂ F := by
    have := (LinearMap.toContinuousLinearMap F).differentiable
    rwa [LinearMap.coe_toContinuousLinearMap'] at this

  have hpt : ∀ z, (u.ex z).left ≫ m ≫ f = (u.ex (F z)).left ≫ m := by
    intro z
    rw [hF z, Over.comp_left, Category.assoc, hf₀]

  have hex0 : u.ex 0 = 1 := (u.ker 0).2 (zero_mem _)
  have hone : (1 : 𝟙_ (Over (Sp ℂ)) ⟶ P₀.A) ≫ f₀ = 1 := by
    have h0 := hF 0
    rw [map_zero, hex0] at h0
    exact h0.symm
  have hFl : ∀ l ∈ u.Λ, F l ∈ u.Λ := by
    intro l hl
    rw [← u.ker, hF, (u.ker l).2 hl, hone]
  have hexF : ∀ z, ∀ l ∈ u.Λ, u.ex (F (z + l)) = u.ex (F z) := by
    intro z l hl
    rw [map_add]
    exact ex_add_lattice u _ _ (hFl l hl)
  have hdom : ∀ W z, z ∈ dom u m (f ⁻¹ᵁ W) ↔ F z ∈ dom u m W := by
    intro W z
    show ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ (f ⁻¹ᵁ W) ↔ ⊤ ≤ ((u.ex (F z)).left ≫ m) ⁻¹ᵁ W
    rw [← hpt z]
    rfl
  have hfn : ∀ W a z, fn u m (f ⁻¹ᵁ W) ((f.app W).hom a) z = fn u m W a (F z) := by
    intro W a z
    show valAt' ((u.ex z).left ≫ m) (f ⁻¹ᵁ W) ((f.app W).hom a) = valAt' ((u.ex (F z)).left ≫ m) W a
    rw [← hpt z, ← Category.assoc, valAt'_comp_lemma ((u.ex z).left ≫ m) f W a]
  have hfd : ∀ W a z, F z ∈ dom u m W → fderiv ℂ (fn u m (f ⁻¹ᵁ W) ((f.app W).hom a)) z =
      (fderiv ℂ (fn u m W a) (F z)).comp (LinearMap.toContinuousLinearMap F) := by
    intro W a z hz
    have e : fn u m (f ⁻¹ᵁ W) ((f.app W).hom a) = fn u m W a ∘ (LinearMap.toContinuousLinearMap F) := by
      funext w
      exact hfn W a w
    rw [e]
    exact ((fn_differentiableAt u m W a (F z) hz).hasFDerivAt.comp z
      (LinearMap.toContinuousLinearMap F).hasFDerivAt).fderiv

  let d : (Fin P₀.g → ℂ) → ∀ W : X.Opens, Γ(X, W) → ℂ :=
    fun z W a => s (F z) W a - s z (f ⁻¹ᵁ W) ((f.app W).hom a)
  have hd : ∀ z, PtDer ((u.ex (F z)).left ≫ m) (d z) ∧ ∀ r, d z ⊤ (constFn p ⊤ r) = 0 := by
    intro z
    refine ⟨?_, ?_⟩
    · have h1 := ptDer_push _ f (s z) (hKS.der z)
      rw [Category.assoc, hpt z] at h1
      exact ptDer_sub _ _ _ (hKS.der (F z)) h1
    · intro r
      have htop : ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ (f ⁻¹ᵁ ⊤) := fun x _ => trivial
      show s (F z) ⊤ (constFn p ⊤ r) - s z (f ⁻¹ᵁ ⊤) ((f.app ⊤).hom (constFn p ⊤ r)) = 0
      rw [app_top_constFn p f hfp r, (hKS.der z).res ⊤ (f ⁻¹ᵁ ⊤) le_top htop, hKS.base, hKS.base, sub_self]
  have hdhol : ∀ W a, DifferentiableOn ℂ (fun z => d z W a) {z ∈ Set.univ | F z ∈ dom u m W} := by
    intro W a
    have h1 : DifferentiableOn ℂ (fun z => s (F z) W a) {z ∈ Set.univ | F z ∈ dom u m W} :=
      (hKS.hol W a).comp hFdiff.differentiableOn (fun z hz => hz.2)
    have h2 : DifferentiableOn ℂ (fun z => s z (f ⁻¹ᵁ W) ((f.app W).hom a)) {z ∈ Set.univ | F z ∈ dom u m W} :=
      (hKS.hol (f ⁻¹ᵁ W) ((f.app W).hom a)).mono (fun z hz => (hdom W z).2 hz.2)
    exact h1.sub h2
  obtain ⟨w, hwd, hw⟩ := GlobalTheory.T.exists_differentiableOn_verticalVectorField P₀ u Hm χ hU R x₀ X p m hp hpb P₀.g Set.univ F d isOpen_univ hFdiff
    (fun z _ => hd z) hdhol

  have hper : ∀ z, ∀ l ∈ u.Λ,
      w (z + l) = w z + (Θ.mulVec (star (F l)) - F (Θ.mulVec (star l))) := by
    intro z l hl
    have hFl' := hFl l hl
    have hpt' : PtDer ((u.ex (F z)).left ≫ m) (d (z + l)) ∧ ∀ r, d (z + l) ⊤ (constFn p ⊤ r) = 0 := by
      rw [← hexF z l hl]
      exact hd (z + l)
    obtain ⟨w0, -, huniq⟩ := GlobalTheory.T.existsUnique_uniformising_vector_vertical_tangent P₀ u Hm χ hU R x₀ X p m hp hpb (F z) (d (z + l)) hpt'.1 hpt'.2
    refine (huniq _ ?_).trans (huniq _ ?_).symm
    · intro W a hz
      have hz' : F (z + l) ∈ dom u m W := by
        show ⊤ ≤ ((u.ex (F (z + l))).left ≫ m) ⁻¹ᵁ W
        rw [hexF z l hl]
        exact hz
      rw [hw (z + l) (Set.mem_univ _) W a hz', map_add, fderiv_fn_add_lattice u m W a (F z) (F l) hFl']
    · intro W a hz
      have hzf : z ∈ dom u m (f ⁻¹ᵁ W) := (hdom W z).2 hz
      have e1 := hKS.per ⟨F l, hFl'⟩ W a (F z) hz
      have e2 := hKS.per ⟨l, hl⟩ (f ⁻¹ᵁ W) ((f.app W).hom a) z hzf
      have hd0 := hw z (Set.mem_univ _) W a hz
      show s (F (z + l)) W a - s (z + l) (f ⁻¹ᵁ W) ((f.app W).hom a) = _
      rw [map_add, e1, e2, hfd W a z hz]
      show _ = fderiv ℂ (fn u m W a) (F z) (w z + (Θ.mulVec (star (F l)) - F (Θ.mulVec (star l))))
      rw [ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap', map_add, map_sub, ← hd0]
      ring

  have hc_add : ∀ v v' : Fin P₀.g → ℂ,
      Θ.mulVec (star (F (v + v'))) - F (Θ.mulVec (star (v + v'))) =
        (Θ.mulVec (star (F v)) - F (Θ.mulVec (star v))) + (Θ.mulVec (star (F v')) - F (Θ.mulVec (star v'))) := by
    intro v v'
    rw [map_add, star_add, star_add, Matrix.mulVec_add, Matrix.mulVec_add, map_add]
    abel
  have hc_smul : ∀ (a : ℂ) (v : Fin P₀.g → ℂ),
      Θ.mulVec (star (F (a • v))) - F (Θ.mulVec (star (a • v))) =
        star a • (Θ.mulVec (star (F v)) - F (Θ.mulVec (star v))) := by
    intro a v
    rw [map_smul, star_smul, star_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, map_smul, smul_sub]
  let cA : (Fin P₀.g → ℂ) →+ (Fin P₀.g → ℂ) :=
    AddMonoidHom.mk' (fun v => Θ.mulVec (star (F v)) - F (Θ.mulVec (star v))) hc_add
  have hexp : ∀ v : Fin P₀.g → ℂ, Θ.mulVec (star (F v)) - F (Θ.mulVec (star v)) =
      ∑ j, star (v j) • cA (fun k => if j = k then 1 else 0) := by
    intro v
    have h1 : cA v = ∑ j, cA (v j • fun k => if j = k then 1 else 0) := by
      conv_lhs => rw [pi_eq_sum_univ v]
      exact map_sum cA _ _
    refine h1.trans (Finset.sum_congr rfl fun j _ => ?_)
    exact hc_smul (v j) _

  have hwdiff : Differentiable ℂ w := differentiableOn_univ.1 hwd
  have hzero : ∀ i j, cA (fun k => if j = k then 1 else 0) i = 0 := by
    intro i j
    have hperi : ∀ (l : u.Λ) (z : Fin P₀.g → ℂ), w (z + l) i =
        w z i + (fun j => cA (fun k => if j = k then 1 else 0) i) ⬝ᵥ star (l : Fin P₀.g → ℂ) := by
      intro l z
      rw [hper z l l.2, Pi.add_apply, hexp (l : Fin P₀.g → ℂ)]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, dotProduct, Pi.star_apply]
      congr 1
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hI := GlobalTheory.T.entire_antilinear_lattice_periods_const P₀.g u.Λ u.discrete u.full (fun z => w z i) _ (differentiable_pi.1 hwdiff i) hperi
    exact congrFun hI.1 j
  intro z
  have hz := hexp z
  have hz0 : Θ.mulVec (star (F z)) - F (Θ.mulVec (star z)) = 0 := by
    rw [hz]
    funext i
    simp [hzero]
  exact (sub_eq_zero.1 hz0).symm
end GlobalTheory.KS.Endo

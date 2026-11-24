-- Prove2me | solution 1 for GlobalTheory.SharpObj.per_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:15:05.818946+00:00
-- url     : https://prove2.me/submissions/e8697682-20a7-47c6-90bf-a67b3a9c5d55

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ImInvIsHermitian
import Theorems.Thm_GlobalTheory_SharpObj_per_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.SharpObj
variable {h : ℕ}
variable {τ : Matrix (Fin h) (Fin h) ℂ}
private theorem re_mulVec_ofRealVec (a : Fin h → ℝ) (i : Fin h) :
    ((τ.mulVec (ReciprocityTheory.PTheta.ofRealVec a)) i).re = ((τ.map Complex.re).mulVec a) i := by
  unfold ReciprocityTheory.PTheta.ofRealVec
  simp [Matrix.mulVec, dotProduct, Complex.re_sum]
private theorem im_mulVec_ofRealVec (a : Fin h → ℝ) (i : Fin h) :
    ((τ.mulVec (ReciprocityTheory.PTheta.ofRealVec a)) i).im = ((τ.map Complex.im).mulVec a) i := by
  unfold ReciprocityTheory.PTheta.ofRealVec
  simp [Matrix.mulVec, dotProduct, Complex.im_sum]
private theorem eq_zero_of_mulVec_ofRealVec_add_eq_zero (hp : (τ.map Complex.im).PosDef) (a b : Fin h → ℝ)
    (hab : τ.mulVec (ReciprocityTheory.PTheta.ofRealVec a) + ReciprocityTheory.PTheta.ofRealVec b = 0) : a = 0 ∧ b = 0 := by
  have hu : IsUnit (τ.map Complex.im).det := (Matrix.isUnit_iff_isUnit_det _).1 hp.isUnit
  have him : (τ.map Complex.im).mulVec a = 0 := by
    funext i
    have := congrArg (fun v => (v i).im) hab
    simp only [Pi.add_apply, Complex.add_im, im_mulVec_ofRealVec, Pi.zero_apply, Complex.zero_im] at this
    simpa [ReciprocityTheory.PTheta.ofRealVec.eq_1] using this
  have ha : a = 0 := by
    calc a = ((τ.map Complex.im)⁻¹ * τ.map Complex.im).mulVec a := by
          rw [Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, him, Matrix.mulVec_zero]
  refine ⟨ha, ?_⟩
  funext i
  have := congrArg (fun v => (v i).re) hab
  simp only [Pi.add_apply, Complex.add_re, re_mulVec_ofRealVec, ha, Matrix.mulVec_zero, Pi.zero_apply,
    Complex.zero_re, zero_add] at this
  simpa [ReciprocityTheory.PTheta.ofRealVec.eq_1] using this
end GlobalTheory.SharpObj
end
end

set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SharpObj
variable {h : ℕ}
variable {τ : Matrix (Fin h) (Fin h) ℂ}
namespace GlobalTheory.SharpObj
theorem _root_.solution (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) :
    Function.Injective (per τ) ∧ DiscreteTopology (LinearMap.range (per τ)) ∧
      Submodule.span ℝ (LinearMap.range (per τ) : Set (Fin h → ℂ)) = ⊤ := by
  obtain ⟨P, hP⟩ : ∃ P : (Fin h ⊕ Fin h → ℝ) →ₗ[ℝ] (Fin h → ℂ), ∀ g, P g =
      τ.mulVec (ReciprocityTheory.PTheta.ofRealVec (fun i => g (.inl i))) + ReciprocityTheory.PTheta.ofRealVec (fun i => g (.inr i)) :=
    ⟨{ toFun := fun g => τ.mulVec (ReciprocityTheory.PTheta.ofRealVec (fun i => g (.inl i))) +
          ReciprocityTheory.PTheta.ofRealVec (fun i => g (.inr i))
       map_add' := fun g g' => by
          funext i
          unfold ReciprocityTheory.PTheta.ofRealVec
          simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Complex.ofReal_add,
            mul_add, Finset.sum_add_distrib]
          ring
       map_smul' := fun c g => by
          funext i
          unfold ReciprocityTheory.PTheta.ofRealVec
          simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.smul_apply,
            smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply, Complex.real_smul, mul_add, Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun _ _ => by ring }, fun _ => rfl⟩
  have hPinj : Function.Injective P := by
    refine (injective_iff_map_eq_zero P).2 fun g hg => ?_
    rw [hP] at hg
    obtain ⟨h1, h2⟩ := eq_zero_of_mulVec_ofRealVec_add_eq_zero hp _ _ hg
    funext j
    cases j with
    | inl i => exact congrFun h1 i
    | inr i => exact congrFun h2 i
  have hper : ∀ x, per τ x = P (fun j => (x j : ℝ)) := fun x => by rw [hP, per_eq]
  have hinj : Function.Injective (per τ) := fun x y hxy => by
    rw [hper, hper] at hxy
    funext j
    exact_mod_cast congrFun (hPinj hxy) j
  have hdim : Module.finrank ℝ (Fin h ⊕ Fin h → ℝ) = Module.finrank ℝ (Fin h → ℂ) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex]
    omega
  set e := P.linearEquivOfInjective hPinj hdim with he
  set b := (Pi.basisFun ℝ (Fin h ⊕ Fin h)).map e with hb
  have hrepr : ∀ w j, b.repr w j = e.symm w j := fun w j => by
    simp [hb, Module.Basis.map_repr]
  have hrange : LinearMap.range (per τ) = Submodule.span ℤ (Set.range b) := by
    ext w
    rw [Module.Basis.mem_span_iff_repr_mem ℤ b w, LinearMap.mem_range]
    simp only [hrepr]
    constructor
    · rintro ⟨x, rfl⟩ j
      refine ⟨x j, ?_⟩
      have : e.symm (P fun j => (x j : ℝ)) = fun j => (x j : ℝ) := e.symm_apply_apply _
      rw [hper, this]
      simp
    · intro hw
      choose n hn using hw
      refine ⟨n, ?_⟩
      have : (fun j => (n j : ℝ)) = e.symm w := funext fun j => by simpa using hn j
      rw [hper, this]
      exact e.apply_symm_apply w
  refine ⟨hinj, ?_, ?_⟩
  · rw [hrange]
    infer_instance
  · rw [hrange, Submodule.span_span_of_tower, b.span_eq]
end GlobalTheory.SharpObj

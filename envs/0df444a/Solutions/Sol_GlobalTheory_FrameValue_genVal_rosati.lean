-- Prove2me | solution 1 for GlobalTheory.FrameValue.genVal_rosati
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:41:27.879707+00:00
-- url     : https://prove2.me/submissions/ff2cf23c-13e9-49ae-bee3-0e76a8b04bd5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ConstOfNormPeriodic
import Theorems.Thm_GlobalTheory_FrameValue_genVal_ne_zero
import Theorems.Thm_GlobalTheory_FrameValue_genVal_pull
import Theorems.Thm_GlobalTheory_FrameValue_genVal_one
import Theorems.Thm_GlobalTheory_FrameValue_genVal_corr
import Theorems.Thm_GlobalTheory_FrameValue_differentiable_genVal
import Theorems.Thm_GlobalTheory_FrameValue_chi_ne_zero
import Theorems.Thm_GlobalTheory_FrameValue_genVal_add_period
import Theorems.Thm_GlobalTheory_FrameValue_const_of_norm_periodic
import Theorems.Thm_GlobalTheory_FrameValue_ahFactor_zero
import Theorems.Thm_GlobalTheory_FrameValue_lift_mem
import Theorems.Thm_GlobalTheory_FrameValue_isLift_rosati
import Theorems.Thm_GlobalTheory_AppellHumbertTrivial_hermForm_add_left
import Theorems.Thm_GlobalTheory_AppellHumbertTrivial_hermForm_smul_left
import Theorems.Thm_GlobalTheory_AppellHumbertTrivial_hermForm_smul_right
import Theorems.Thm_GlobalTheory_CubeValues_ex_add_period
import Theorems.Thm_GlobalTheory_CubeValues_ex_zero
import Theorems.Thm_GlobalTheory_EigenNorm_hermForm_add_left
import Theorems.Thm_GlobalTheory_EigenNorm_hermForm_conj
import Theorems.Thm_GlobalTheory_EigenNorm_hermForm_smul_left
import Theorems.Thm_GlobalTheory_EigenNorm_hermForm_smul_right
import Theorems.Thm_GlobalTheory_entire_apply_eq_of_periodic_of_span_real


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
noncomputable section
open GlobalTheory GlobalTheory.FrameValue
open CubeValues SymmetricSemicharacter EigenNorm
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g}
  {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
variable [IsCommMonObj A] {f f' : A ⟶ A} {F G : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)}
namespace GlobalTheory.FrameValue
theorem _root_.solution (hL : L.IsLB) (h : u.IsAH Hm χ) (hF : ∀ z, u.ex (F z) = u.ex z ≫ f)
    (hG : ∀ z, u.ex (G z) = u.ex z ≫ f') (r : LB.Gen (LB.LinComb L (Out.rosatiφ A f f') Out.rosatiε)) (hr : r.IsGen)
    (h₀ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ r (Out.zero2 A)) (LB.oneGen L)) :
    (∀ x z, hermForm Hm (F x) z = hermForm Hm x (G z)) ∧
      ∀ x z, genVal u hL r (lift (u.ex x) (u.ex z)).left (rosatiLift F G x z) = 1 := by
  obtain ⟨V, hV⟩ : ∃ V : (Fin g → ℂ) → (Fin g → ℂ) → ℂ,
      ∀ x z, V x z = genVal u hL r (lift (u.ex x) (u.ex z)).left (rosatiLift F G x z) := ⟨_, fun _ _ => rfl⟩
  have dF : Differentiable ℂ F := (LinearMap.toContinuousLinearMap F).differentiable
  have dG : Differentiable ℂ G := (LinearMap.toContinuousLinearMap G).differentiable
  have d₁ : ∀ z, Differentiable ℂ fun x => V x z := fun z => by
    have hp : ∀ w, (u.ex w).left ≫ (lift (𝟙 A) (toUnit A ≫ u.ex z)).left = (lift (u.ex w) (u.ex z)).left := fun w => by
      rw [← Over.comp_left]
      congr 1
      simp [comp_lift, Subsingleton.elim (toUnit (𝟙_ (Over (Sp ℂ)))) (𝟙 _)]
    have := differentiable_genVal hL hr _ (q := id) differentiable_id (z := fun w => rosatiLift F G w z)
      (fun k => by fin_cases k <;> simp [rosatiLift] <;> fun_prop)
      (fun w => by rw [id, hp]; exact isLift_rosati hF hG w z)
    simpa only [id, hp, hV] using this
  have d₂ : ∀ x, Differentiable ℂ fun z => V x z := fun x => by
    have hp : ∀ w, (u.ex w).left ≫ (lift (toUnit A ≫ u.ex x) (𝟙 A)).left = (lift (u.ex x) (u.ex w)).left := fun w => by
      rw [← Over.comp_left]
      congr 1
      simp [comp_lift, Subsingleton.elim (toUnit (𝟙_ (Over (Sp ℂ)))) (𝟙 _)]
    have := differentiable_genVal hL hr _ (q := id) differentiable_id (z := fun w => rosatiLift F G x w)
      (fun k => by fin_cases k <;> simp [rosatiLift] <;> fun_prop)
      (fun w => by rw [id, hp]; exact isLift_rosati hF hG x w)
    simpa only [id, hp, hV] using this
  have p₁ : ∀ (l : u.Λ) x z, V (x + l) z =
      Complex.exp (Real.pi * (hermForm Hm z (F l) - hermForm Hm (G z) l)) * V x z := fun l x z => by
    have e₂ : rosatiLift F G (x + l) z = fun k => rosatiLift F G x z k +
        ((![⟨F l, lift_mem hF l⟩, ⟨F l, lift_mem hF l⟩, 0, l, l, 0] : Fin 6 → u.Λ) k : Fin g → ℂ) := by
      funext k
      fin_cases k <;> simp [rosatiLift] <;> abel
    rw [hV, hV, ex_add_period u x l l.2, e₂, genVal_add_period hL h r (isLift_rosati hF hG x z)]
    congr 1
    have n := chi_ne_zero h l
    have n' := chi_ne_zero h ⟨F l, lift_mem hF l⟩
    simp only [Fin.prod_univ_six, rosatiLift, Out.rosatiε, Matrix.cons_val, ahFactor_zero hL h, zpow_neg, zpow_one]
    simp only [ahFactor, hermForm_add_left, mul_add, mul_sub, Complex.exp_add, Complex.exp_sub]
    field_simp
  have p₂ : ∀ (l : u.Λ) x z, V x (z + l) =
      Complex.exp (Real.pi * (hermForm Hm (F x) l - hermForm Hm x (G l))) * V x z := fun l x z => by
    have e₂ : rosatiLift F G x (z + l) = fun k => rosatiLift F G x z k +
        ((![l, 0, l, ⟨G l, lift_mem hG l⟩, 0, ⟨G l, lift_mem hG l⟩] : Fin 6 → u.Λ) k : Fin g → ℂ) := by
      funext k
      fin_cases k <;> simp [rosatiLift] <;> abel
    rw [hV, hV, ex_add_period u z l l.2, e₂, genVal_add_period hL h r (isLift_rosati hF hG x z)]
    congr 1
    have n := chi_ne_zero h l
    have n' := chi_ne_zero h ⟨G l, lift_mem hG l⟩
    simp only [Fin.prod_univ_six, rosatiLift, Out.rosatiε, Matrix.cons_val, ahFactor_zero hL h, zpow_neg, zpow_one]
    simp only [ahFactor, hermForm_add_left, mul_add, mul_sub, Complex.exp_add, Complex.exp_sub]
    field_simp
  have ne : ∀ x z, V x z ≠ 0 := fun x z => (hV x z).symm ▸ genVal_ne_zero hL r (isLift_rosati hF hG x z)

  obtain ⟨B, hB⟩ : ∃ B : (Fin g → ℂ) → (Fin g → ℂ) → ℂ, ∀ x z, B x z = hermForm Hm (F x) z - hermForm Hm x (G z) :=
    ⟨_, fun _ _ => rfl⟩
  have Bc : ∀ x z, hermForm Hm z (F x) - hermForm Hm (G z) x = starRingEnd ℂ (B x z) := fun x z => by
    rw [hB, map_sub, ← hermForm_conj Hm h.1, ← hermForm_conj Hm h.1]
  have Ba : ∀ x y z, B (x + y) z = B x z + B y z := fun x y z => by
    simp only [hB, map_add, hermForm_add_left]; ring
  have Bs : ∀ (c : ℂ) x z, B (c • x) z = c * B x z := fun c x z => by
    simp only [hB, map_smul, hermForm_smul_left]; ring
  have Bs' : ∀ (c : ℂ) x z, B x (c • z) = starRingEnd ℂ c * B x z := fun c x z => by
    simp only [hB, map_smul, hermForm_smul_right]; ring
  have Bd : ∀ z, Differentiable ℂ fun x => B x z := fun z => by
    simp only [hB, hermForm, dotProduct]
    fun_prop
  have k₁ : ∀ (l : u.Λ) z, Complex.exp (Real.pi * starRingEnd ℂ (B l z)) = Complex.exp (Real.pi * B l z) := fun l z => by
    have hc := const_of_norm_periodic u (F := fun x => V x z * Complex.exp (-(Real.pi * B x z)))
      ((d₁ z).mul (((Bd z).const_mul _).neg.cexp)) (fun m x => by
        simp only [p₁, Bc, Ba, norm_mul, Complex.norm_exp]
        rw [mul_comm (Real.exp _), _root_.mul_assoc, ← Real.exp_add]
        congr 2
        simp
        ring) (0 + l) 0
    have B0 : B 0 z = 0 := by simpa using Bs 0 0 z
    simp only [p₁] at hc
    simp only [Bc, B0, zero_add, mul_zero, neg_zero, Complex.exp_zero, _root_.mul_one, Complex.exp_neg] at hc
    have n := ne 0 z
    have n' := Complex.exp_ne_zero (Real.pi * B l z)
    field_simp at hc
    exact hc
  have k₂ : ∀ (l : u.Λ) z, (B l z).im = 0 := fun l z => by
    by_contra hne
    have := k₁ l ((((2 * (B l z).im)⁻¹ : ℝ) : ℂ) • z)
    rw [Bs', Complex.conj_ofReal] at this
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 this
    have hi := congrArg Complex.im hn
    simp only [Complex.mul_im, Complex.add_im, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat,
      zero_mul, mul_zero, add_zero, sub_zero, _root_.mul_one] at hi
    have hpi := Real.pi_ne_zero
    field_simp at hi
    have : (2 * n + 1 : ℤ) = 0 := by
      have : (2 * n + 1 : ℝ) = 0 := by linarith
      exact_mod_cast this
    omega
  have k₃ : ∀ (l : u.Λ) z, B l z = 0 := fun l z => by
    have := k₂ l (Complex.I • z)
    rw [Bs'] at this
    exact Complex.ext (by simpa using this) (k₂ l z)
  have k₄ : ∀ x z, B x z = 0 := fun x z => by
    have hx : x ∈ Submodule.span ℝ (u.Λ : Set (Fin g → ℂ)) := by rw [u.full]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy => exact k₃ ⟨y, hy⟩ z
    | zero => simpa using Bs 0 0 z
    | add a b _ _ ha hb => rw [Ba, ha, hb, add_zero]
    | smul c a _ ha => rw [← Complex.coe_smul, Bs, ha, mul_zero]
  have c₁ : ∀ x z, V x z = V 0 z := fun x z => entire_apply_eq_of_periodic_of_span_real (d₁ z) u.full
    (fun w l hl => by simpa [Bc, k₄] using p₁ ⟨l, hl⟩ w z) x 0
  have c₂ : ∀ x z, V x z = V x 0 := fun x z => entire_apply_eq_of_periodic_of_span_real (d₂ x) u.full
    (fun w l hl => by simpa [← hB, k₄] using p₂ ⟨l, hl⟩ x w) z 0
  refine ⟨fun x z => sub_eq_zero.1 ((hB x z).symm.trans (k₄ x z)), fun x z => ?_⟩
  rw [← hV, c₁, c₂, hV]
  have e : (lift (u.ex 0) (u.ex 0)).left = 𝟙 (Sp ℂ) ≫ Out.zero2 A := by rw [ex_zero, Hom.one_def]; simp
  have hz := isLift_rosati hF hG 0 0
  rw [e] at hz ⊢
  rw [← genVal_pull, ← genVal_one (u := u) hL (𝟙 (Sp ℂ)) PEmpty.elim]
  refine genVal_corr hL h₀ (fun k => (Category.assoc _ _ _).symm.trans (hz k)) (fun k => k.elim) fun f => ?_
  simp [Fin.prod_univ_six, rosatiLift, Out.rosatiε]
end GlobalTheory.FrameValue

-- Prove2me | solution 1 for NumberField.TateGlobal.differentiable_and_eulerProduct_mul_prod_mul_partialEulerProduct_eq_one_and_prod_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/d6e1b9fb-cfa4-59af-960a-3dcfc2bcd8f0

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_NormPowChar

import Theorems.Thm_NumberField_multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one
import Theorems.Thm_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt
import Theorems.Thm_NumberField_TateGlobal_localChar_apply_eq_apply_uniformizerIdele_of_isUnramifiedCharAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_differentiable_and_eulerProduct_mul_prod_mul_partialEulerProduct_eq_one_and_prod_ne_zero

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open NumberField.TateGlobal
open scoped Classical

open NumberField.AdelicLevel in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ϖ : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletion K)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion K) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hχu : AutomorphicForm.IsUnitaryChar (𝓞 K) K χ)
    (hunr : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → IsUnramifiedCharAt χ v) :
    let P : ℂ → ℂ := fun w => ∏' v : HeightOneSpectrum (𝓞 K),
        (1 - (if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹
    let FS : ℂ → ℂ := fun w => ∏ v ∈ S,
        (1 - (if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)))
    Differentiable ℂ FS ∧
    (∀ w : ℂ, 1 < w.re →
      P w * FS w * (∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
        (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w))) = 1) ∧
    (∀ w : ℂ, 0 < w.re →
      FS w ≠ 0 ∧ (∏ v ∈ S, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-w.re))) ≤ ‖FS w‖) := by
  intro P FS
  have hN2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    intro v
    have h1 : 1 < Ideal.absNorm v.asIdeal := by
      refine lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr ?_) ?_
      · rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
      · intro h; exact v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h.symm)
    exact_mod_cast h1
  have hNpos : ∀ v : HeightOneSpectrum (𝓞 K), (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) :=
    fun v => by linarith [hN2 v]
  have hNnat : ∀ v : HeightOneSpectrum (𝓞 K), 0 < Ideal.absNorm v.asIdeal :=
    fun v => by exact_mod_cast hNpos v
  have hN0 : ∀ v : HeightOneSpectrum (𝓞 K), ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 :=
    fun v => by exact_mod_cast (hNpos v).ne'
  have ha1 : ∀ v : HeightOneSpectrum (𝓞 K),
      ‖(if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0)‖ ≤ 1 := by
    intro v
    split_ifs
    · exact (hχu _).le
    · simp
  have hNcpow : ∀ (v : HeightOneSpectrum (𝓞 K)) (w : ℂ),
      ‖(((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w))‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-w.re) := by
    intro v w
    rw [Complex.norm_natCast_cpow_of_pos (hNnat v), Complex.neg_re]
  have hε : ∀ (v : HeightOneSpectrum (𝓞 K)) (w : ℂ),
      ‖(if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
        (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w))‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-w.re) := by
    intro v w
    rw [norm_mul, hNcpow]
    calc _ ≤ 1 * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-w.re) :=
          mul_le_mul_of_nonneg_right (ha1 v) (Real.rpow_nonneg (hNpos v).le _)
      _ = _ := one_mul _
  have hlt1 : ∀ (v : HeightOneSpectrum (𝓞 K)) (w : ℂ), 0 < w.re →
      ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-w.re) < 1 := by
    intro v w hw
    exact Real.rpow_lt_one_of_one_lt_of_neg (by linarith [hN2 v]) (by linarith)
  have hfac : ∀ (v : HeightOneSpectrum (𝓞 K)) (w : ℂ), 0 < w.re →
      (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-w.re)) ≤
        ‖1 - (if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w))‖ := by
    intro v w hw
    have h := norm_sub_norm_le (1 : ℂ) ((if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)))
    rw [norm_one] at h
    linarith [hε v w]
  refine ⟨?_, ?_, ?_⟩
  ·
    show Differentiable ℂ fun w : ℂ => ∏ v ∈ S,
      (1 - (if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
        (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)))
    have h : Differentiable ℂ (∏ v ∈ S, fun w : ℂ =>
        (1 - (if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)))) :=
      Differentiable.finsetProd fun v _ =>
        (differentiable_const _).sub ((differentiable_const _).mul
          (differentiable_id.neg.const_cpow (Or.inl (hN0 v))))
    rw [Finset.prod_fn] at h
    exact h
  ·
    intro w hw
    have hw0 : 0 < w.re := by linarith
    set f : HeightOneSpectrum (𝓞 K) → ℂ := fun v =>
      1 - (if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
        (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)) with hf
    have hsum : Summable fun v : HeightOneSpectrum (𝓞 K) =>
        -((if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w))) := by
      refine (Summable.of_norm_bounded (NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt K hw)
        (fun v => ?_))
      rw [norm_neg]
      exact hε v w
    have hfeq : ∀ v : HeightOneSpectrum (𝓞 K), f v =
        1 + -((if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w))) := fun v => sub_eq_add_neg _ _
    have hfne : ∀ v : HeightOneSpectrum (𝓞 K), f v ≠ 0 := by
      intro v h0
      have := hfac v w hw0
      rw [show (1 - (if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w))) = f v from rfl, h0, norm_zero] at this
      linarith [hlt1 v w hw0]
    have hmulF : Multipliable f := by
      rw [show f = fun v => 1 + -((if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w))) from funext hfeq]
      exact Complex.multipliable_one_add_of_summable hsum
    have hmulG : Multipliable fun v : HeightOneSpectrum (𝓞 K) => (f v)⁻¹ := by
      have h98 := (NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one K ∅
        (fun v => (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0))
        (fun v => ha1 v.1)).1 w hw
      let e : {v : HeightOneSpectrum (𝓞 K) // v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 K)))} ≃
          HeightOneSpectrum (𝓞 K) := Equiv.subtypeUnivEquiv (fun v => Finset.notMem_empty v)
      exact (Equiv.multipliable_iff e).mp h98
    have hPF : P w * (∏' v : HeightOneSpectrum (𝓞 K), f v) = 1 := by
      show (∏' v : HeightOneSpectrum (𝓞 K), (f v)⁻¹) * _ = 1
      rw [← hmulG.tprod_mul hmulF]
      have : ∀ v : HeightOneSpectrum (𝓞 K), (f v)⁻¹ * f v = 1 := fun v => inv_mul_cancel₀ (hfne v)
      simp only [this, tprod_one]
    have hS : Multipliable (f ∘ ((↑) : ((↑S : Set (HeightOneSpectrum (𝓞 K)))) → _)) :=
      Multipliable.of_finite
    have hSc : Multipliable (f ∘ ((↑) : (↑(↑S : Set (HeightOneSpectrum (𝓞 K)))ᶜ) → _)) := by
      have h2 := Complex.multipliable_one_add_of_summable
        (hsum.subtype ((↑S : Set (HeightOneSpectrum (𝓞 K)))ᶜ))
      convert h2 using 1
      rfl
      rfl
      rfl
    have hsplit := hS.tprod_mul_tprod_compl hSc
    rw [Finset.tprod_subtype' S f] at hsplit
    have hES : (∏' v : (↑(↑S : Set (HeightOneSpectrum (𝓞 K)))ᶜ), f v) =
        ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
          (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w)) := by
      show (∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, f v.1) = _
      refine tprod_congr fun v => ?_
      show (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w))) = _
      rw [if_pos (hunr v.1 v.2),
        NumberField.TateGlobal.localChar_apply_eq_apply_uniformizerIdele_of_isUnramifiedCharAt K χ v.1
          (hunr v.1 v.2) (ϖ v.1) (hϖ v.1)]
    rw [← hES, mul_assoc]
    show P w * ((∏ v ∈ S, f v) * _) = 1
    rw [hsplit]
    exact hPF
  ·
    intro w hw
    have hnorm : ‖FS w‖ = ∏ v ∈ S, ‖1 - (if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w))‖ := norm_prod _ _
    have hle : (∏ v ∈ S, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-w.re))) ≤ ‖FS w‖ := by
      rw [hnorm]
      refine Finset.prod_le_prod (fun v _ => by linarith [hlt1 v w hw]) fun v _ => hfac v w hw
    have hpos : 0 < ∏ v ∈ S, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-w.re)) :=
      Finset.prod_pos fun v _ => by linarith [hlt1 v w hw]
    refine ⟨?_, hle⟩
    intro h0
    rw [h0, norm_zero] at hle
    linarith

end S_NumberField_TateGlobal_differentiable_and_eulerProduct_mul_prod_mul_partialEulerProduct_eq_one_and_prod_ne_zero
end P2MW
export P2MW.S_NumberField_TateGlobal_differentiable_and_eulerProduct_mul_prod_mul_partialEulerProduct_eq_one_and_prod_ne_zero (solution)

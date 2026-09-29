-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_localZeta30_localZetaDual31_eulerData_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/62a4b5b9-8ef5-5ff9-9a59-24455347017d

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_localZeta30_localZetaDual31_eulerData_of_forall

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 6400000

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker

open LanglandsTunnell.CubicInduction
open scoped Matrix NNReal ENNReal

noncomputable section

namespace T31Engine

section Algebra

variable {A : Type*} [CommRing A]

theorem transposeInv3_coe (g : GL (Fin 3) A) :
    ((transposeInv3 g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      (((g⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ := rfl

theorem transposeInv3_mul (g h : GL (Fin 3) A) :
    transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h := by
  refine Units.ext ?_
  rw [Units.val_mul, transposeInv3_coe, transposeInv3_coe, transposeInv3_coe, _root_.mul_inv_rev, Units.val_mul,
    Matrix.transpose_mul]

theorem transposeInv3_transposeInv3 (g : GL (Fin 3) A) : transposeInv3 (transposeInv3 g) = g := by
  refine Units.ext ?_
  show ((((g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ)ᵀ = _
  exact Matrix.transpose_transpose _

theorem dual_point (Y g h : GL (Fin 3) A) :
    longWeyl3 * transposeInv3 (Y * (weylPrime3 * transposeInv3 g)) * h =
      longWeyl3 * transposeInv3 (Y * (weylPrime3 * transposeInv3 (g * h))) := by
  simp only [transposeInv3_mul, transposeInv3_transposeInv3, mul_assoc]

end Algebra

section Measures

variable (v : HeightOneSpectrum (𝓞 ℚ))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem borelSpace_units : BorelSpace (v.adicCompletion ℚ)ˣ := by
  refine ⟨?_⟩
  have hind : (inferInstance : TopologicalSpace (v.adicCompletion ℚ)ˣ) =
      TopologicalSpace.induced Units.val inferInstance :=
    (Units.isEmbedding_val₀ (G₀ := v.adicCompletion ℚ)).eq_induced
  show MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace (v.adicCompletion ℚ)) =
    borel (v.adicCompletion ℚ)ˣ
  rw [BorelSpace.measurable_eq (α := v.adicCompletion ℚ), ← borel_comap, ← hind]

theorem isAddHaarMeasure_selfDualHaarAt : (selfDualHaarAt ℚ v).IsAddHaarMeasure := by
  set c : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ v) : ℝ) / 2)
    with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (NNReal.rpow_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot))).ne'
  have hdef : selfDualHaarAt ℚ v = (c : ℝ≥0∞) • Measure.addHaarMeasure (integersPositiveCompacts ℚ v) := rfl
  rw [hdef]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc0) ENNReal.coe_ne_top

scoped instance sigmaFinite_selfDual : SigmaFinite (selfDualHaarAt ℚ v) := by
  haveI := isAddHaarMeasure_selfDualHaarAt v
  infer_instance

theorem secondCountableTopology_units : SecondCountableTopology (v.adicCompletion ℚ)ˣ := by
  haveI : SecondCountableTopology (v.adicCompletion ℚ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

scoped instance sigmaFinite_mulHaar :
    SigmaFinite (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)) : Measure (v.adicCompletion ℚ)ˣ) := by
  haveI := isAddHaarMeasure_selfDualHaarAt v
  haveI := borelSpace_units v
  haveI := LanglandsTunnell.TateLocal.isHaarMeasure_comap_val_mulMeasure ℚ v (selfDualHaarAt ℚ v)
  haveI := secondCountableTopology_units v
  infer_instance

end Measures

section Pack

variable (v : HeightOneSpectrum (𝓞 ℚ)) (E Ed : Polynomial ℂ) (ε : ℂ) (ℓ : ℕ)

def Pack (X : LocalGL3 v → ℂ) (g : LocalGL3 v) : Prop :=
      (letI := localBorel ℚ v
       ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q R : Polynomial ℂ) (m : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
          P s * R.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
            Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) X 1 g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) X 1 s g =
            (E.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
        IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
          (selfDualHaarAt ℚ v) (dualWhittakerFn3 X) 1 (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
              X 1 (1 - s) g =
            (Ed.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ *
              ((ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s))) * P s))

variable {v E Ed ε ℓ}

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

local notation "qv" => (Ideal.absNorm (HeightOneSpectrum.asIdeal v) : ℂ)
local notation "μu" => (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)) : Measure (v.adicCompletion ℚ)ˣ)
local notation "νa" => selfDualHaarAt ℚ v

theorem qv_ne_zero : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)

theorem pack_translate {X : LocalGL3 v → ℂ} {g : LocalGL3 v} (h : LocalGL3 v) (hX : Pack v E Ed ε ℓ X (g * h)) :
    Pack v E Ed ε ℓ (fun x => X (x * h)) g := by
  obtain ⟨P, σ₀, σ₁, hrat, hc30, hid30, hc31, hid31⟩ := hX
  refine ⟨P, σ₀, σ₁, hrat, ?_, ?_, ?_, ?_⟩
  · intro s hs
    have := hc30 s hs
    simpa only [mul_assoc] using this
  · intro s hs
    rw [← hid30 s hs]
    simp only [localZeta30, mul_assoc]
  · intro s hs
    have := hc31 s hs
    simpa only [dualWhittakerFn3_apply, dual_point] using this
  · intro s hs
    rw [← hid31 s hs]
    simp only [localZetaDual31, localZeta31, dualWhittakerFn3_apply, dual_point]

theorem pack_zero (g : LocalGL3 v) : Pack v E Ed ε ℓ 0 g := by
  refine ⟨0, 0, 0, ⟨0, 1, 0, one_ne_zero, fun s => by simp⟩, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact (integrable_zero _ _ _).congr (Filter.Eventually.of_forall fun a => by simp)
  · intro s hs; simp [localZeta30]
  · intro s hs
    exact (integrable_zero _ _ _).congr (Filter.Eventually.of_forall fun a => by simp [dualWhittakerFn3_apply])
  · intro s hs; simp [localZetaDual31, localZeta31, dualWhittakerFn3_apply]

theorem pack_smul {X : LocalGL3 v → ℂ} {g : LocalGL3 v} (c : ℂ) (hX : Pack v E Ed ε ℓ X g) :
    Pack v E Ed ε ℓ (c • X) g := by
  obtain ⟨P, σ₀, σ₁, ⟨Q, R, m, hR, hrat⟩, hc30, hid30, hc31, hid31⟩ := hX
  refine ⟨fun s => c * P s, σ₀, σ₁, ⟨Polynomial.C c * Q, R, m, hR, fun s => ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [Polynomial.eval_mul, Polynomial.eval_C, mul_assoc, hrat s]; ring
  · intro s hs
    refine ((hc30 s hs).const_mul c).congr (Filter.Eventually.of_forall fun a => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  · intro s hs
    have h := hid30 s hs
    simp only [localZeta30] at h ⊢
    have : (∫ a, (c • X) (iotaGL (diagUnitGL2 a) * g) * (((1 : (v.adicCompletion ℚ)ˣ →* ℂˣ) a : ℂˣ) : ℂ) *
        ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) ∂μu) =
        c * ∫ a, X (iotaGL (diagUnitGL2 a) * g) * (((1 : (v.adicCompletion ℚ)ˣ →* ℂˣ) a : ℂˣ) : ℂ) *
        ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) ∂μu := by
      rw [← integral_const_mul]; congr 1; funext a; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [this, h]; ring
  · intro s hs
    refine ((hc31 s hs).const_mul c).congr (Filter.Eventually.of_forall fun a => ?_)
    simp only [dualWhittakerFn3_apply, Pi.smul_apply, smul_eq_mul]; ring
  · intro s hs
    have h := hid31 s hs
    simp only [localZetaDual31, localZeta31] at h ⊢
    have hin : ∀ a : (v.adicCompletion ℚ)ˣ,
        (∫ x, dualWhittakerFn3 (c • X) (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x *
          (weylPrime3 * transposeInv3 g)) ∂νa) =
        c * ∫ x, dualWhittakerFn3 X (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x *
          (weylPrime3 * transposeInv3 g)) ∂νa := by
      intro a
      rw [← integral_const_mul]; congr 1
    simp only [hin]
    have : (∫ a, c * (∫ x, dualWhittakerFn3 X (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x *
          (weylPrime3 * transposeInv3 g)) ∂νa) * ((((1 : (v.adicCompletion ℚ)ˣ →* ℂˣ)⁻¹ a : ℂˣ)) : ℂ) *
        ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 - s - 1) ∂μu) =
        c * ∫ a, (∫ x, dualWhittakerFn3 X (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x *
          (weylPrime3 * transposeInv3 g)) ∂νa) * ((((1 : (v.adicCompletion ℚ)ˣ →* ℂˣ)⁻¹ a : ℂˣ)) : ℂ) *
        ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 - s - 1) ∂μu := by
      rw [← integral_const_mul]; congr 1; funext a; ring
    rw [this, h]; ring

theorem cpow_book (m n : ℕ) (s : ℂ) :
    ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ n * (Ideal.absNorm v.asIdeal : ℂ) ^ (((m + n : ℕ) : ℂ) * s) =
      (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s) := by
  rw [← Complex.cpow_nat_mul, ← Complex.cpow_add _ _ qv_ne_zero]
  congr 1
  push_cast
  ring

theorem pack_add {X Y : LocalGL3 v → ℂ} {g : LocalGL3 v} (hX : Pack v E Ed ε ℓ X g) (hY : Pack v E Ed ε ℓ Y g) :
    Pack v E Ed ε ℓ (X + Y) g := by
  obtain ⟨P₁, σ₀, σ₁, ⟨Q₁, R₁, m₁, hR₁, hrat₁⟩, hc30, hid30, hc31, hid31⟩ := hX
  obtain ⟨P₂, σ₀', σ₁', ⟨Q₂, R₂, m₂, hR₂, hrat₂⟩, hc30', hid30', hc31', hid31'⟩ := hY
  refine ⟨fun s => P₁ s + P₂ s, max σ₀ σ₀', max σ₁ σ₁',
    ⟨Q₁ * R₂ * Polynomial.X ^ m₂ + Q₂ * R₁ * Polynomial.X ^ m₁, R₁ * R₂, m₁ + m₂, mul_ne_zero hR₁ hR₂, fun s => ?_⟩,
    ?_, ?_, ?_, ?_⟩
  ·
    have h1 := hrat₁ s
    have h2 := hrat₂ s
    have hb1 := cpow_book (v := v) m₁ m₂ s
    have hb2 := cpow_book (v := v) m₂ m₁ s
    rw [add_comm m₂ m₁] at hb2
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    have e1 : (Q₁.eval (qv ^ (-s)) * R₂.eval (qv ^ (-s)) * (qv ^ (-s)) ^ m₂) * qv ^ (((m₁ + m₂ : ℕ) : ℂ) * s) =
        Q₁.eval (qv ^ (-s)) * qv ^ ((m₁ : ℂ) * s) * R₂.eval (qv ^ (-s)) := by
      rw [← hb1]; ring
    have e2 : (Q₂.eval (qv ^ (-s)) * R₁.eval (qv ^ (-s)) * (qv ^ (-s)) ^ m₁) * qv ^ (((m₁ + m₂ : ℕ) : ℂ) * s) =
        Q₂.eval (qv ^ (-s)) * qv ^ ((m₂ : ℂ) * s) * R₁.eval (qv ^ (-s)) := by
      rw [← hb2]; ring
    calc (P₁ s + P₂ s) * (R₁.eval (qv ^ (-s)) * R₂.eval (qv ^ (-s)))
        = (P₁ s * R₁.eval (qv ^ (-s))) * R₂.eval (qv ^ (-s)) + (P₂ s * R₂.eval (qv ^ (-s))) * R₁.eval (qv ^ (-s)) := by
          ring
      _ = Q₁.eval (qv ^ (-s)) * qv ^ ((m₁ : ℂ) * s) * R₂.eval (qv ^ (-s)) +
          Q₂.eval (qv ^ (-s)) * qv ^ ((m₂ : ℂ) * s) * R₁.eval (qv ^ (-s)) := by rw [h1, h2]
      _ = (Q₁.eval (qv ^ (-s)) * R₂.eval (qv ^ (-s)) * (qv ^ (-s)) ^ m₂ +
            Q₂.eval (qv ^ (-s)) * R₁.eval (qv ^ (-s)) * (qv ^ (-s)) ^ m₁) * qv ^ (((m₁ + m₂ : ℕ) : ℂ) * s) := by
          rw [add_mul, e1, e2]
  · intro s hs
    have h := (hc30 s (lt_of_le_of_lt (le_max_left _ _) hs)).add (hc30' s (lt_of_le_of_lt (le_max_right _ _) hs))
    refine h.congr (Filter.Eventually.of_forall fun a => ?_)
    simp only [Pi.add_apply]; ring
  · intro s hs
    have hs₁ : σ₀ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have hs₂ : σ₀' < s.re := lt_of_le_of_lt (le_max_right _ _) hs
    have h := hid30 s hs₁
    have h' := hid30' s hs₂
    have hI := hc30 s hs₁
    have hI' := hc30' s hs₂
    simp only [localZeta30] at h h' ⊢
    have hsplit : (∫ a, (X + Y) (iotaGL (diagUnitGL2 a) * g) * (((1 : (v.adicCompletion ℚ)ˣ →* ℂˣ) a : ℂˣ) : ℂ) *
        ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) ∂μu) =
        (∫ a, X (iotaGL (diagUnitGL2 a) * g) * (((1 : (v.adicCompletion ℚ)ˣ →* ℂˣ) a : ℂˣ) : ℂ) *
          ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) ∂μu) +
        ∫ a, Y (iotaGL (diagUnitGL2 a) * g) * (((1 : (v.adicCompletion ℚ)ˣ →* ℂˣ) a : ℂˣ) : ℂ) *
          ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) ∂μu := by
      rw [← integral_add hI hI']; congr 1; funext a; simp only [Pi.add_apply]; ring
    rw [hsplit, h, h']; ring
  · intro s hs
    have h := (hc31 s (lt_of_le_of_lt (le_max_left _ _) hs)).add (hc31' s (lt_of_le_of_lt (le_max_right _ _) hs))
    refine h.congr (Filter.Eventually.of_forall fun a => ?_)
    simp only [dualWhittakerFn3_apply, Pi.add_apply]; ring
  · intro s hs
    have hs₁ : σ₁ < (1 - s).re := lt_of_le_of_lt (le_max_left _ _) hs
    have hs₂ : σ₁' < (1 - s).re := lt_of_le_of_lt (le_max_right _ _) hs
    have h := hid31 s hs₁
    have h' := hid31' s hs₂
    have hI := hc31 (1 - s) hs₁
    have hI' := hc31' (1 - s) hs₂
    simp only [localZetaDual31, localZeta31] at h h' ⊢

    have key : ∀ (Z : LocalGL3 v → ℂ),
        Integrable (fun p : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ =>
          dualWhittakerFn3 Z (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * (weylPrime3 * transposeInv3 g)) *
            (((1 : (v.adicCompletion ℚ)ˣ →* ℂˣ) p.1 : ℂˣ) : ℂ) *
            ((modulus (p.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 - s - 1)) (Measure.prod μu νa) →
        (∫ a, (∫ x, dualWhittakerFn3 Z (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x *
            (weylPrime3 * transposeInv3 g)) ∂νa) * ((((1 : (v.adicCompletion ℚ)ˣ →* ℂˣ)⁻¹ a : ℂˣ)) : ℂ) *
            ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 - s - 1) ∂μu) =
        ∫ p : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ,
          dualWhittakerFn3 Z (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * (weylPrime3 * transposeInv3 g)) *
            (((1 : (v.adicCompletion ℚ)ˣ →* ℂˣ) p.1 : ℂˣ) : ℂ) *
            ((modulus (p.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 - s - 1) ∂(Measure.prod μu νa) := by
      intro Z hZ
      rw [integral_prod _ hZ]
      congr 1; funext a
      rw [← integral_mul_const, ← integral_mul_const]
      congr 1
    rw [key (X + Y) ((hI.add hI').congr (Filter.Eventually.of_forall fun p => by
        simp only [dualWhittakerFn3_apply, Pi.add_apply]; ring)),
      key X hI, key Y hI'] at *
    have hsplit : (∫ p : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ,
          dualWhittakerFn3 (X + Y) (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * (weylPrime3 * transposeInv3 g)) *
            (((1 : (v.adicCompletion ℚ)ˣ →* ℂˣ) p.1 : ℂˣ) : ℂ) *
            ((modulus (p.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 - s - 1) ∂(Measure.prod μu νa)) =
        (∫ p : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ,
          dualWhittakerFn3 X (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * (weylPrime3 * transposeInv3 g)) *
            (((1 : (v.adicCompletion ℚ)ˣ →* ℂˣ) p.1 : ℂˣ) : ℂ) *
            ((modulus (p.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 - s - 1) ∂(Measure.prod μu νa)) +
        ∫ p : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ,
          dualWhittakerFn3 Y (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * (weylPrime3 * transposeInv3 g)) *
            (((1 : (v.adicCompletion ℚ)ˣ →* ℂˣ) p.1 : ℂˣ) : ℂ) *
            ((modulus (p.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 - s - 1) ∂(Measure.prod μu νa) := by
      rw [← integral_add hI hI']; congr 1; funext p; simp only [dualWhittakerFn3_apply, Pi.add_apply]; ring
    rw [hsplit, h, h']; ring

end Pack

end T31Engine
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_localZeta30_localZetaDual31_eulerData_of_forall.T31Engine"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_localZeta30_localZetaDual31_eulerData_of_forall.T31Engine"

open T31Engine in
theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (W : LocalGL3 v → ℂ) (E Ed : Polynomial ℂ) (ε : ℂ) (ℓ : ℕ)
    (h31 : ∀ g : LocalGL3 v,
      (letI := localBorel ℚ v
       ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q R : Polynomial ℂ) (m : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
          P s * R.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
            Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 s g =
            (E.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
        IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
          (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) 1 (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
              W 1 (1 - s) g =
            (Ed.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ *
              ((ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s))) * P s))) :
    ∀ W' ∈ gl3CyclicSubspace W, ∀ g : LocalGL3 v,
      (letI := localBorel ℚ v
       ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q R : Polynomial ℂ) (m : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
          P s * R.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
            Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W' 1 g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W' 1 s g =
            (E.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
        IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
          (selfDualHaarAt ℚ v) (dualWhittakerFn3 W') 1 (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
              W' 1 (1 - s) g =
            (Ed.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ *
              ((ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s))) * P s)) := by
  intro W' hW'
  induction hW' using Submodule.span_induction with
  | mem X hX =>
    obtain ⟨h, rfl⟩ := hX
    intro g
    exact pack_translate h (h31 (g * h))
  | zero => intro g; exact pack_zero g
  | add X Y _ _ ihX ihY => intro g; exact pack_add (ihX g) (ihY g)
  | smul c X _ ih => intro g; exact pack_smul c (ih g)

end S_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_localZeta30_localZetaDual31_eulerData_of_forall
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_localZeta30_localZetaDual31_eulerData_of_forall (solution)

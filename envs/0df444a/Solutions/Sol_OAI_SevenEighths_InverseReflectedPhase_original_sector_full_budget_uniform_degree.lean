-- Prove2me | solution 1 for OAI.SevenEighths.InverseReflectedPhase.original_sector_full_budget_uniform_degree
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T04:06:15.646351+00:00
-- url     : https://prove2.me/submissions/c4a719ec-c11f-467d-98b5-caa1445bfc28

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B026
import Definitions.Def_OAIHecke78B028
import Theorems.Thm_OAI_SevenEighths_InverseReflectedPhase_original_family_whole_tail_uniform_degree
import Theorems.Thm_OAI_SevenEighths_InverseReflectedPhase_original_sector_retained_energy_uniform_degree

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.DyadicColumns
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

theorem columnDyadicLength_small_power (ε : ℝ) (hε : 0 < ε) (N : ℝ) (hN : 1 ≤ N) :
    (columnDyadicLength N + 1 : ℝ) ≤ (2 + 1 / (ε * Real.log 2)) * N ^ ε := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : 0 ≤ Real.log N / Real.log 2 := div_nonneg (Real.log_nonneg hN) hlog.le
  have hceil := Nat.ceil_lt_add_one hq
  have hL : (columnDyadicLength N + 1 : ℝ) ≤ 2 + Real.log N / Real.log 2 := by
    dsimp only [columnDyadicLength]
    linarith
  have hr : 1 ≤ N ^ ε := Real.one_le_rpow hN hε.le
  have hb : Real.log N / Real.log 2 ≤ (N ^ ε / ε) / Real.log 2 :=
    div_le_div_of_nonneg_right (Real.log_le_rpow_div (by linarith) hε) hlog.le
  calc
    _ ≤ 2 + Real.log N / Real.log 2 := hL
    _ ≤ 2 * N ^ ε + (N ^ ε / ε) / Real.log 2 := add_le_add (by linarith) hb
    _ = _ := by field_simp

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson UnrestrictedIdealReindex QuadraticSquarefreeKernel

end CanonicalQuadraticSieve

open scoped BigOperators Classical

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.Canonical
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

namespace PrimeFamily
variable {ι : Type*} (G : PrimeFamily ι)

lemma generator_product [Fintype ι] :
    (∏ i, G.generator i) = primaryGenerator (∏ i, G.ideal i) := by
  change _ = primaryGeneratorHom (∏ i, G.ideal i)
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact primaryPrime_eq_primaryGenerator (G.ideal i)

end PrimeFamily

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.Shape
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CubicKubota ConcreteTraceCRT CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma shapeArgument_mul (x y : Eis) : shapeArgument (x*y) = shapeArgument x*shapeArgument y := by
  unfold shapeArgument
  rw [← Ideal.span_singleton_mul_span_singleton,map_mul,Nat.cast_mul,Complex.ofReal_mul,map_mul,mul_pow]
  exact mul_div_mul_comm _ _ _ _

lemma shapeArgument_norm (z : Eis) (hz : z ≠ 0) : ‖shapeArgument z‖ = 1 := by
  have hne : ‖eisEmbedding z‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hz))
  rw [shapeArgument,norm_div,norm_pow,Complex.norm_real,Real.norm_of_nonneg (Nat.cast_nonneg _),
    ← eisEmbedding_norm_sq_eq_absNorm_span]
  exact div_self hne

lemma stratumShapeFactor_mul {H : Matrix.SpecialLinearGroup (Fin 2) Eis}
    (s : FixedCuspShape H) (c r P : Eis) :
    s.stratumShapeFactor (c*r*P) = s.stratumShapeFactor c*shapeArgument r*shapeArgument P := by
  have he (z : Eis) : s.stratumShapeFactor z =
      (-star (levelTwoComplexCharacter s.gamma)*eisEmbedding (s.upper 0 0)^2)*shapeArgument z := by
    unfold FixedCuspShape.stratumShapeFactor shapeArgument
    ring
  rw [he (c*r*P),he c,shapeArgument_mul,shapeArgument_mul]
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.DyadicBox
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CompletedGauss CompletedDyadic CanonicalQuadraticSieve
noncomputable section

lemma retainedDyadicBox_card (scale B : ℝ) :
    (retainedDyadicBox scale B).card=(columnDyadicLength (max 1 (B/scale))+1)^3 := by
  simp only [retainedDyadicBox,Finset.card_product,Finset.card_range]
  ring

theorem retainedDyadicBox_count_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ scale B : ℝ,
      ((retainedDyadicBox scale B).card:ℝ)^2≤C*(max 1 (B/scale))^ε := by
  refine ⟨(2+1/((ε/6)*Real.log 2))^6,by positivity,?_⟩
  intro scale B
  have hR : 1≤ max 1 (B/scale) := le_max_left _ _
  have hp : 0< max 1 (B/scale) := lt_of_lt_of_le zero_lt_one hR
  have hh := columnDyadicLength_small_power (ε/6) (by positivity) _ hR
  rw [retainedDyadicBox_card]
  push_cast
  rw [← pow_mul]
  norm_num only [show (3:ℕ)*2=6 by norm_num]
  apply (pow_le_pow_left₀ (by positivity) hh 6).trans_eq
  rw [mul_pow,← Real.rpow_mul_natCast hp.le]
  congr 2
  ring
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.TailAbsorption
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma familyRawScale_reciprocal {φ : Type*} [Fintype φ] {a c : Eis} {mode : Bool}
    (F : PrimeFamily φ) (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (X QK QP : ℝ) :
    (familyRawScale F s X QK QP^2)⁻¹=
      (27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2)^2*
        (Ideal.absNorm (∏ i,F.ideal i):ℝ)^4*QK^4*QP^4*(X⁻¹)^2 := by
  unfold familyRawScale actualKernelCoefficient fixedKernelCoefficient
  simp only [ramifiedScale,pow_zero,map_mul,map_one,Nat.cast_mul,Nat.cast_one,one_pow,mul_one]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv,mul_pow,inv_pow]
  ring

lemma family_tail_polynomial_cap {φ : Type*} [Fintype φ] {a c : Eis} {mode : Bool}
    (F : PrimeFamily φ) (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (Z X QK QP Lcap : ℝ) (hZ : 0<Z) (hQK : 0≤QK) (hQP : 0≤QP) (hX : 0<X)
    (hF : (Ideal.absNorm (∏ i,F.ideal i):ℝ)≤Z^Lcap)
    (hK : QK≤Z^Lcap) (hP : QP≤Z^Lcap) (hXi : X⁻¹≤Z^Lcap) :
    ((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*(familyRawScale F s X QK QP^2)⁻¹≤
      (27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2)^2*Z^(17*Lcap) := by
  rw [familyRawScale_reciprocal]
  calc
    _ = (27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2)^2*
        ((Ideal.absNorm (∏ i,F.ideal i):ℝ)^5*QK^5*QP^5*(X⁻¹)^2) := by ring
    _ ≤ (27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2)^2*
        ((Z^Lcap)^5*(Z^Lcap)^5*(Z^Lcap)^5*(Z^Lcap)^2) := by gcongr
    _ = _ := by
      rw [←pow_add,←pow_add,←pow_add,←Real.rpow_mul_natCast hZ.le]
      norm_num only [Nat.reduceAdd,Nat.cast_ofNat]
      rw [mul_comm Lcap 17]

theorem choose_rapid_tail_order (Lcap δ saving : ℝ) (hδ : 0<δ) :
    ∃ A : ℕ, ∀ Z : ℝ, 1≤Z →
      (Z^δ)^(-(A:ℝ))*Z^Lcap≤Z^(-saving) := by
  obtain ⟨A,hA⟩ := exists_nat_gt ((Lcap+saving)/δ)
  refine ⟨A,?_⟩
  intro Z hZ
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  rw [←Real.rpow_mul hz.le,←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ
  have hh := (div_lt_iff₀ hδ).mp hA
  nlinarith

theorem choose_weighted_rapid_tail_order (Lcap Lextra δ saving : ℝ) (hδ : 0<δ) :
    ∃ A : ℕ, ∀ Z E : ℝ, 1≤Z → 0≤E → E≤Z^Lextra →
      E*(Z^δ)^(-(A:ℝ))*Z^Lcap≤Z^(-saving) := by
  obtain ⟨A,hA⟩ := choose_rapid_tail_order (Lcap+Lextra) δ saving hδ
  refine ⟨A,?_⟩
  intro Z E hZ hE he
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  calc
    _ ≤ Z^Lextra*(Z^δ)^(-(A:ℝ))*Z^Lcap := by gcongr
    _ = (Z^δ)^(-(A:ℝ))*Z^(Lcap+Lextra) := by rw [Real.rpow_add hz]; ring
    _ ≤ _ := hA Z hZ
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.ActualSizeCaps
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma finite_ideal_count_polynomial (rows : Finset (Ideal Eis)) (Z H Lcap : ℝ)
    (hZ : 128≤Z) (hH : 1≤H) (hn : ∀ I∈rows,I≠0)
    (hbound : ∀ I∈rows,(Ideal.absNorm I:ℝ)≤H) (hcap : H≤Z^Lcap) :
    (rows.card:ℝ)≤Z^(Lcap+1) := by
  have hz : 0<Z := by linarith
  calc
    _ ≤ 128*H := DescentFiberCost.finite_ideal_count_real rows H hH hn hbound
    _ ≤ Z*Z^Lcap := mul_le_mul hZ hcap (by linarith) hz.le
    _ = _ := by rw [Real.rpow_add hz,Real.rpow_one];ring

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.TailEnergyBudgetUniformDegree
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem actual_row_tail_energy_budget_uniform_degree
    (Lcap Lcount δ saving : ℝ) (hδ : 0<δ) :
    ∃ A : ℕ, ∀ {a c : Eis} {mode : Bool}
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)), ∀ {φ : Type*} [Fintype φ] (F : PrimeFamily φ)
      (Z X QK QP nrow nslot : ℝ),
      1≤Z → 0<X → 0≤QK → 0≤QP → 0≤nrow → 0≤nslot →
      (Ideal.absNorm (∏ i,F.ideal i):ℝ)≤Z^Lcap →
      QK≤Z^Lcap → QP≤Z^Lcap → X⁻¹≤Z^Lcap →
      nrow≤Z^Lcount → nslot≤Z^Lcount →
      nrow*(nslot*((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*
        (Z^δ)^(-(A:ℝ))*(familyRawScale F s X QK QP^2)⁻¹)^2≤
      (27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2)^4*Z^(-saving) := by
  obtain ⟨A,hA⟩ := choose_weighted_rapid_tail_order (17*Lcap) Lcount δ ((saving+Lcount)/2) hδ
  refine ⟨A,?_⟩
  intro a c mode s φ _ F Z X QK QP nrow nslot hZ hX hQK hQP hnrow hnslot hF hK hP hXi hrow hslot
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  let cusp := 27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2
  have hcusp : 0≤ cusp := by dsimp [cusp];positivity
  have hs := family_tail_polynomial_cap F s Z X QK QP Lcap hz hQK hQP hX hF hK hP hXi
  have ha := hA Z nslot hZ hnslot hslot
  have hb : nslot*((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*(Z^δ)^(-(A:ℝ))*
        (familyRawScale F s X QK QP^2)⁻¹≤ cusp^2*Z^(-((saving+Lcount)/2)) := by
    calc
      _ = (nslot*(Z^δ)^(-(A:ℝ)))*
          (((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*(familyRawScale F s X QK QP^2)⁻¹) := by ring
      _ ≤ (nslot*(Z^δ)^(-(A:ℝ)))*(cusp^2*Z^(17*Lcap)) := by
        exact mul_le_mul_of_nonneg_left hs (by positivity)
      _ = cusp^2*(nslot*(Z^δ)^(-(A:ℝ))*Z^(17*Lcap)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ha (sq_nonneg _)
  calc
    _ ≤ Z^Lcount*(cusp^2*Z^(-((saving+Lcount)/2)))^2 := by gcongr
    _ = cusp^4*Z^(Lcount+(-((saving+Lcount)/2))*2) := by
      rw [mul_pow,←pow_mul,←Real.rpow_mul_natCast hz.le,Real.rpow_add hz]
      ring_nf
    _ = _ := by congr 2;ring
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.ActualSizeCapsUniformDegree
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem actual_finite_source_tail_budget_uniform_degree
    (Lcap δ saving : ℝ) (hδ : 0<δ) :
    ∃ A : ℕ, ∀ {a c : Eis} {mode : Bool}
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)), ∀ {φ : Type*} [Fintype φ] (F : PrimeFamily φ)
      (rows Pset : Finset (Ideal Eis)) (Z X QK QP : ℝ),
      128≤Z → 0<X → 1≤QK → 1≤QP →
      (∀ K∈rows,K≠0 ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,P≠0 ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (Ideal.absNorm (∏ i,F.ideal i):ℝ)≤Z^Lcap →
      QK≤Z^Lcap → QP≤Z^Lcap → X⁻¹≤Z^Lcap →
      (rows.card:ℝ)*(Pset.card*((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*
        (Z^δ)^(-(A:ℝ))*(familyRawScale F s X QK QP^2)⁻¹)^2≤
      (27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2)^4*Z^(-saving) := by
  obtain ⟨A,hA⟩ := actual_row_tail_energy_budget_uniform_degree Lcap (Lcap+1) δ saving hδ
  refine ⟨A,?_⟩
  intro a c mode s φ _ F rows Pset Z X QK QP hZ hX hQK hQP hrows hPs hF hK hP hXi
  have hz : 1≤Z := by linarith
  exact hA s F Z X QK QP rows.card Pset.card hz hX (by linarith) (by linarith)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hF hK hP hXi
    (finite_ideal_count_polynomial rows Z QK Lcap hZ hQK (fun K hK => (hrows K hK).1) (fun K hK => (hrows K hK).2) hK)
    (finite_ideal_count_polynomial Pset Z QP Lcap hZ hQP (fun P hP => (hPs P hP).1) (fun P hP => (hPs P hP).2) hP)
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.CountBudget
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve
noncomputable section

lemma retained_count_le_box (scale B : ℝ) :
    (retainedDyads scale B).card≤(retainedDyadicBox scale B).card :=
  Finset.card_filter_le _ _

lemma cutoff_ratio_cap (Z scale δ Lscale : ℝ) (hZ : 1≤Z) (hδL : 0≤δ+Lscale)
    (hscale : scale⁻¹≤Z^Lscale) :
    max 1 (16*Z^δ/scale)≤16*Z^(δ+Lscale) := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  apply max_le
  · have hp : 1≤Z^(δ+Lscale) := Real.one_le_rpow hZ hδL
    linarith
  · rw [Real.rpow_add hz,div_eq_mul_inv,←mul_assoc]
    exact mul_le_mul_of_nonneg_left hscale (by positivity)

theorem retained_count_budget (ε δ Lscale : ℝ) (hε : 0<ε) (hδL : 0≤δ+Lscale) :
    ∃ C : ℝ, 0<C ∧ ∀ Z scale : ℝ, 1≤Z → scale⁻¹≤Z^Lscale →
      ((retainedDyads scale (16*Z^δ)).card:ℝ)^2≤C*Z^ε := by
  let α := ε/(1+δ+Lscale)
  have ha : 0<α := div_pos hε (by linarith)
  obtain ⟨C,hC,hcount⟩ := retainedDyadicBox_count_small_power α ha
  refine ⟨C*16^α,by positivity,?_⟩
  intro Z scale hZ hscale
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hpow : α*(δ+Lscale)≤ε := by
    have he : α*(1+δ+Lscale)=ε := by dsimp [α];field_simp [ne_of_gt (show 0<1+δ+Lscale from by linarith)]
    nlinarith
  calc
    _ ≤ ((retainedDyadicBox scale (16*Z^δ)).card:ℝ)^2 := by
      apply pow_le_pow_left₀ (Nat.cast_nonneg _)
      exact_mod_cast retained_count_le_box scale (16*Z^δ)
    _ ≤ C*(max 1 (16*Z^δ/scale))^α := hcount _ _
    _ ≤ C*(16*Z^(δ+Lscale))^α := by
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (cutoff_ratio_cap Z scale δ Lscale hZ hδL hscale) ha.le) hC.le
    _ = (C*16^α)*Z^((δ+Lscale)*α) := by rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hz.le _),←Real.rpow_mul hz.le];ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)) (by positivity)

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.ShapeWeights
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma stratumShapeFactor_mul_one {H : Matrix.SpecialLinearGroup (Fin 2) Eis}
    (s : FixedCuspShape H) (c r : Eis) :
    s.stratumShapeFactor (c*r)=s.stratumShapeFactor c*shapeArgument r := by
  simpa only [mul_one,shapeArgument_one] using stratumShapeFactor_mul s c r 1

lemma primeFamily_primary_product_ne_zero {φ : Type*} [Fintype φ] (F : PrimeFamily φ) :
    primaryGenerator (∏ i,F.ideal i)≠0 := by
  rw [←F.generator_product]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => F.generator_ne_zero i)

lemma stratumShapeFactor_frozen_norm {φ : Type*} [Fintype φ]
    {H : Matrix.SpecialLinearGroup (Fin 2) Eis} (s : FixedCuspShape H) (c : Eis) (F : PrimeFamily φ) :
    ‖s.stratumShapeFactor (c*primaryGenerator (∏ i,F.ideal i))‖=‖s.stratumShapeFactor c‖ := by
  rw [stratumShapeFactor_mul_one,norm_mul,shapeArgument_norm _ (primeFamily_primary_product_ne_zero F),mul_one]

lemma row_shape_weight_norm (r : Ideal Eis→ℂ) (K : Ideal Eis) (hK : Admissible K) :
    ‖r K*shapeArgument (primaryGenerator K)‖=‖r K‖ := by
  have hk := PrimaryIdealUnitReindex.primaryGenerator_ne_zero_of_good_factors K hK.1 (fun P hP => (hK.2.2 P hP).1)
  rw [norm_mul,shapeArgument_norm _ hk,mul_one]

lemma slot_shape_weight_norm (aw : Ideal Eis→ℂ) (P : Ideal Eis) (hP : CubicSieve.Admissible P) :
    ‖aw P*shapeArgument (primaryGenerator P)‖=‖aw P‖ := by
  rw [norm_mul,shapeArgument_norm _ hP.2,mul_one]
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.FullEnergyBasic
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
noncomputable section

lemma norm_sq_le_retained (f g : ℂ) (E : ℝ) (_hE : 0≤E) (hf : ‖f-g‖≤E) :
    ‖f‖^2≤2*‖g‖^2+2*E^2 := by
  have hh : ‖f‖≤‖g‖+E := by
    calc
      _ = ‖g+(f-g)‖ := by congr 1;ring
      _ ≤ ‖g‖+‖f-g‖ := norm_add_le _ _
      _ ≤ _ := add_le_add_right hf _
  have hsq := pow_le_pow_left₀ (norm_nonneg f) hh 2
  nlinarith [sq_nonneg (‖g‖-E)]

lemma row_energy_le_retained {α : Type*} (rows : Finset α) (f g : α→ℂ) (E : ℝ)
    (hE : 0≤E) (hf : ∀ k∈rows,‖f k-g k‖≤E) :
    (∑ k∈rows,‖f k‖^2)≤2*(∑ k∈rows,‖g k‖^2)+2*rows.card*E^2 := by
  calc
    _ ≤ ∑ k∈rows, (2*‖g k‖^2+2*E^2) := Finset.sum_le_sum (fun k hk => norm_sq_le_retained (f k) (g k) E hE (hf k hk))
    _ = _ := by simp only [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,nsmul_eq_mul];ring
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.RetainedBudgetUniformDegree
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v

theorem original_sector_retained_budget_uniform_degree
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (_hLpool : 0≤Lpool) :
    ∃ (degree : ℕ), ∀ {Nlevel a c₀ : Eis} {mode : Bool}
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (_hNlevel : (9:Eis)*c₀∣Nlevel)
    (_hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (_hac : IsCoprime a c₀),
    ∃ (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F B R Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hB : B≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<Cf → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      (Ideal.absNorm F:ℝ)≤Cf*Z^V →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      Real.log (widthConstant B Ck CO CH Cf)/Real.log Z≤η →
      CanonicalMargins F₀ M (normWidth Z R) z₀ margin → F₀=N+V →
      Nstar=N-3*hhat → V≤d → hhat≤d+η →
      H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤M → 0≤O₀ → 0≤za → za≤z₀ →
      0<cstar → cstar/2≤ margin → d≤ cstar/200 →
      η≤ cstar/1000 → δ+η≤ cstar/1000 → π≤ cstar/1000 →
      QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lpool → κ+ρ*Lpool≤ cstar/16 →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=Nlevel) G rows Pset S hrows s hc₀),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∀ (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖∑' u : Eisˣ,∑ i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ),
        literalDyadicRow G K.val (hrows K.val K.property) S j Pset
          (E.completion K) s hc₀ u i W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^(F₀-3*cstar/16-O₀/2) := by
  obtain ⟨degree,huniform⟩ := original_sector_retained_energy_uniform_degree ε hε lo hi hlo W hWs hW ρ hρ η hηpos
  refine ⟨degree,?_⟩
  intro Nlevel a c₀ mode s hc₀ hNlevel hbase hac
  obtain ⟨C,Z₀,hC,hZ₀,henergy⟩ := huniform (Nlevel:=Nlevel) (a:=a) (c₀:=c₀) (mode:=mode) s hc₀ hNlevel hbase hac
  obtain ⟨Cd,hCd,hcount⟩ := retained_count_budget κ δ Lscale hκ hδL
  refine ⟨C*Cd,Z₀,mul_pos hC hCd,hZ₀,?_⟩
  intro σ _ J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap hpool hsmall rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  have hz' : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hzpos : 0<Z := lt_trans zero_lt_one hz'
  have hs := henergy J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP Lscale Lrow Lslot
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget hscap
    rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  have hd := hcount Z (familyRawScale G s X QK QP) hz'.le hscap
  have hp : (Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ≤Z^(Lpool*ρ) := by
    rw [Real.rpow_mul hzpos.le]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hpool hρ.le
  apply hs.trans
  calc
    _ ≤ C*(Cd*Z^κ)*(1+‖θ‖)^degree*Z^(Lpool*ρ)*Z^(F₀-cstar/4-O₀/2) := by gcongr
    _ = (C*Cd)*(1+‖θ‖)^degree*Z^(κ+Lpool*ρ+(F₀-cstar/4-O₀/2)) := by
      rw [Real.rpow_add hzpos,Real.rpow_add hzpos]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hz'.le (by nlinarith only [hsmall])) (by positivity)
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.OriginalFullUniformDegree
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v

private lemma mul_chain_add_one (a b c d e f : ℝ)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f) :
    a*b*c*d*e*f ≤ a*(b+1)*c*d*e*f :=
  mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) ha) hc) hd) he) hf

theorem original_sector_full_energy_uniform_degree
    (Adecay : ℕ) (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (hLpool : 0≤Lpool) :
    ∃ (degree degreeTail : ℕ), ∀ {Nlevel a c₀ : Eis} {mode : Bool}
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (_hNlevel : (9:Eis)*c₀∣Nlevel)
    (_hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (_hac : IsCoprime a c₀),
     ∃ (C Ctail Z₀ : ℝ), 0<C ∧ 0<Ctail ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F B R Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hB : B≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<Cf → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      (Ideal.absNorm F:ℝ)≤Cf*Z^V →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      Real.log (widthConstant B Ck CO CH Cf)/Real.log Z≤η →
      CanonicalMargins F₀ M (normWidth Z R) z₀ margin → F₀=N+V →
      Nstar=N-3*hhat → V≤d → hhat≤d+η →
      H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤M → 0≤O₀ → 0≤za → za≤z₀ →
      0<cstar → cstar/2≤ margin → d≤ cstar/200 →
      η≤ cstar/1000 → δ+η≤ cstar/1000 → π≤ cstar/1000 →
      QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lpool → κ+ρ*Lpool≤ cstar/16 →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=Nlevel) G rows Pset S hrows s hc₀),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∀ (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖literalWholeRow G K.val (hrows K.val K.property) S j Pset
        (E.completion K) s hc₀ W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^(F₀-3*cstar/16-O₀/2)+
          2*rows.card*(Pset.card*Ctail*(1+‖θ‖)^degreeTail*
            ((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*(Z^δ)^(-(Adecay:ℝ))*
            (familyRawScale G s X QK QP^2)⁻¹)^2 := by
  obtain ⟨degree,hu⟩ := original_sector_retained_budget_uniform_degree
    ε hε lo hi hlo W hWs hW ρ hρ η hηpos κ δ Lscale Lpool hκ hδL hLpool
  obtain ⟨degreeTail,Ct,hCt,htail⟩ := original_family_whole_tail_uniform_degree lo hi hlo Adecay W hWs hW
  refine ⟨degree,degreeTail,?_⟩
  intro Nlevel a c₀ mode s hc₀ hNlevel hbase hac
  obtain ⟨Cm,Z₀,hCm,hZ₀,henergy⟩ := hu (Nlevel:=Nlevel) (a:=a) (c₀:=c₀) (mode:=mode) s hc₀ hNlevel hbase hac
  let Cshape := ‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c₀‖
  let Ctail := 6*Cshape*Ct+1
  have hshape : 0≤Cshape := by dsimp [Cshape];positivity
  have hCtail : 0<Ctail := by dsimp [Ctail];positivity
  refine ⟨2*Cshape^2*Cm+1,Ctail,Z₀,by positivity,hCtail,hZ₀,?_⟩
  intro σ _ J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap hpool hsmall rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  let rr := fun K => r K*shapeArgument (primaryGenerator K)
  let aa := fun P => aw P*shapeArgument (primaryGenerator P)
  let Φ := fixedRadialCoefficientScalar*s.stratumShapeFactor (c₀*primaryGenerator (∏ b,G.ideal b))
  let g := fun K : rows => ∑' u : Eisˣ,∑ i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ),
    literalDyadicRow G K.val (hrows K.val K.property) S j Pset (E.completion K) s hc₀ u i W θ X rr aa
  let f := fun K : rows => literalWholeRow G K.val (hrows K.val K.property) S j Pset (E.completion K) s hc₀ W θ X r aw
  let Et := (Pset.card:ℝ)*Ctail*(1+‖θ‖)^degreeTail*((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*
    (Z^δ)^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹
  have hzpos : 0<Z := lt_trans zero_lt_one (lt_of_lt_of_le hZ₀ hZ)
  have hEt : 0≤Et := by dsimp [Et];positivity
  have hΦ : ‖Φ‖=Cshape := by
    dsimp only [Φ,Cshape]
    rw [norm_mul,stratumShapeFactor_frozen_norm]
  have hmain := henergy J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget hscap hpool hsmall
    rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ rr aa hqk hqp hKr hPr
    (fun K hK => by simpa only [rr,row_shape_weight_norm r K (hrows K hK)] using hr K hK)
    (fun P hP => by simpa only [aa,slot_shape_weight_norm aw P (hPr P hP).1] using haw P hP)
  have hrem (K : rows) : ‖f K-Φ*g K‖≤Et := by
    have hodd : ∀ P∈Pset,∀ b,ringChar (Eis⧸(G.reflected K.val (hrows K.val K.property) (S P)).ideal b)≠2 := by
      intro P hP b
      rcases b with b | b | b
      · exact hGchar b
      · exact ((hrows K.val K.property).2.2 b.val (Multiset.mem_toFinset.mp b.property)).2
      · exact hSchar P hP (Sum.inr b)
    have hj : ∀ b : A,j b<6 := by intro b;exact Nat.mod_lt _ (by norm_num)
    have hh := htail (N:=Nlevel) (a:=a) (c:=c₀) (mode:=mode) G K.val (hrows K.val K.property) S j Pset (E.completion K) s hc₀ hNlevel hbase
      hodd hj hprod (fun P hP => (hPr P hP).1) θ X (Z^δ) QK QP r aw hX
      (Real.rpow_pos_of_pos hzpos _) hQK hQP (hKr K.val K.property).2
      (fun P hP => (hPr P hP).2.2) (hr K.val K.property) haw
    apply hh.trans
    change _ ≤ Et
    dsimp only [Et,Ctail,Cshape]
    have he : (6*‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c₀‖)*Pset.card*
        (Ct*(1+‖θ‖)^degreeTail*((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*(Z^δ)^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹)=
      Pset.card*(6*(‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c₀‖)*Ct)*(1+‖θ‖)^degreeTail*
        ((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*(Z^δ)^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹ := by ring
    rw [he]
    apply mul_chain_add_one
    · exact Nat.cast_nonneg _
    · exact pow_nonneg (add_nonneg zero_le_one (norm_nonneg θ)) _
    · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hQK.le) hQP.le
    · exact Real.rpow_nonneg (Real.rpow_nonneg hzpos.le _) _
    · exact inv_nonneg.mpr (sq_nonneg _)
  have hh := row_energy_le_retained (Finset.univ:Finset rows) f (fun K => Φ*g K) Et hEt (fun K _ => hrem K)
  simp only [norm_mul,mul_pow,hΦ,←Finset.mul_sum,Finset.card_univ,Fintype.card_coe] at hh
  apply hh.trans
  calc
    _ ≤ 2*(Cshape^2*(Cm*(1+‖θ‖)^degree*Z^(F₀-3*cstar/16-O₀/2)))+2*rows.card*Et^2 := by gcongr
    _ ≤ _ := by
      dsimp only [Et]
      have hp : 0≤(1+‖θ‖)^degree*Z^(F₀-3*cstar/16-O₀/2) := by positivity
      nlinarith only [hp]
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.FullBudgetUniformDegree
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v

theorem original_sector_full_budget_uniform_degree_oai
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (hLpool : 0≤Lpool)
    (Lcap saving : ℝ) (hδ : 0<δ) :
    ∃ (degree : ℕ), ∀ {Nlevel a c₀ : Eis} {mode : Bool}
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (_hNlevel : (9:Eis)*c₀∣Nlevel)
    (_hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (_hac : IsCoprime a c₀),
     ∃ (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F B R Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hB : B≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<Cf → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      (Ideal.absNorm F:ℝ)≤Cf*Z^V →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      Real.log (widthConstant B Ck CO CH Cf)/Real.log Z≤η →
      CanonicalMargins F₀ M (normWidth Z R) z₀ margin → F₀=N+V →
      Nstar=N-3*hhat → V≤d → hhat≤d+η →
      H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤M → 0≤O₀ → 0≤za → za≤z₀ →
      0<cstar → cstar/2≤ margin → d≤ cstar/200 →
      η≤ cstar/1000 → δ+η≤ cstar/1000 → π≤ cstar/1000 →
      QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      X⁻¹≤Z^Lcap → QK≤Z^Lcap → QP≤Z^Lcap → -saving≤F₀-3*cstar/16-O₀/2 →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lcap →
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lpool → κ+ρ*Lpool≤ cstar/16 →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=Nlevel) G rows Pset S hrows s hc₀),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∀ (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖literalWholeRow G K.val (hrows K.val K.property) S j Pset
        (E.completion K) s hc₀ W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^(F₀-3*cstar/16-O₀/2) := by
  obtain ⟨Adecay,htail⟩ := actual_finite_source_tail_budget_uniform_degree Lcap δ saving hδ
  obtain ⟨degree,degreeTail,hu⟩ := original_sector_full_energy_uniform_degree
    Adecay ε hε lo hi hlo W hWs hW ρ hρ η hηpos κ δ Lscale Lpool hκ hδL hLpool
  refine ⟨max degree (degreeTail*2),?_⟩
  intro Nlevel a c₀ mode s hc₀ hNlevel hbase hac
  obtain ⟨Cm,Ct,Z₀,hCm,hCt,hZ₀,henergy⟩ := hu (Nlevel:=Nlevel) (a:=a) (c₀:=c₀) (mode:=mode) s hc₀ hNlevel hbase hac
  let cusp := 27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c₀}):ℝ)^2
  let deg := max degree (degreeTail*2)
  refine ⟨Cm+2*Ct^2*cusp^4+1,max Z₀ 128,by positivity,
    lt_of_lt_of_le hZ₀ (le_max_left _ _),?_⟩
  intro σ _ J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
  dsimp only
  intro hFcap hscap hpool hsmall rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  have hz' : 1<Z := lt_of_lt_of_le hZ₀ ((le_max_left _ _).trans hZ)
  have hzpos : 0<Z := lt_trans zero_lt_one hz'
  have h128 : 128≤Z := (le_max_right _ _).trans hZ
  have hs := henergy J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot
    ((le_max_left _ _).trans hZ) hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget hscap hpool hsmall
    rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  have ht := htail s G rows Pset Z X QK QP h128 hX hqk (by linarith only [hqp])
    (fun K hK => ⟨(hrows K hK).1,(hKr K hK).2⟩)
    (fun P hP => ⟨(hPr P hP).1.1.ne_zero,(hPr P hP).2.2⟩) hFcap hKcap hPcap hXi
  have hheight : 1≤1+‖θ‖ := by linarith only [norm_nonneg θ]
  have hdm : (1+‖θ‖)^degree≤(1+‖θ‖)^deg := pow_le_pow_right₀ hheight (le_max_left _ _)
  have hdt : (1+‖θ‖)^(degreeTail*2)≤(1+‖θ‖)^deg := pow_le_pow_right₀ hheight (le_max_right _ _)
  have he := Real.rpow_le_rpow_of_exponent_le hz'.le hexp
  apply hs.trans
  have htailbound : 2*rows.card*(Pset.card*Ct*(1+‖θ‖)^degreeTail*
        ((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*(Z^δ)^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹)^2≤
      (2*Ct^2*cusp^4)*(1+‖θ‖)^deg*Z^(F₀-3*cstar/16-O₀/2) := by
    calc
      _ = (2*Ct^2*(1+‖θ‖)^(degreeTail*2))*
          (rows.card*(Pset.card*((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*
            (Z^δ)^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹)^2) := by rw [pow_mul];ring
      _ ≤ (2*Ct^2*(1+‖θ‖)^(degreeTail*2))*(cusp^4*Z^(-saving)) := by
        exact mul_le_mul_of_nonneg_left ht (by positivity)
      _ ≤ (2*Ct^2*(1+‖θ‖)^deg)*(cusp^4*Z^(F₀-3*cstar/16-O₀/2)) := by gcongr
      _ = _ := by ring
  have hmain : Cm*(1+‖θ‖)^degree*Z^(F₀-3*cstar/16-O₀/2)≤
      Cm*(1+‖θ‖)^deg*Z^(F₀-3*cstar/16-O₀/2) := by gcongr
  apply (add_le_add hmain htailbound).trans
  have hp : 0≤(1+‖θ‖)^deg*Z^(F₀-3*cstar/16-O₀/2) := by positivity
  nlinarith only [hp]
end
end SevenEighths.InverseReflectedPhase

end OAI
end

theorem solution.{v} : type_of% @OAI.SevenEighths.InverseReflectedPhase.original_sector_full_budget_uniform_degree_oai.{v} := @OAI.SevenEighths.InverseReflectedPhase.original_sector_full_budget_uniform_degree_oai.{v}

-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.canonical_energy_exists_of_references
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T04:50:49.640012+00:00
-- url     : https://prove2.me/submissions/3da81253-0c55-4190-82d7-7a144adc1ef8

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B024
import Theorems.Thm_OAI_SevenEighths_InverseMoment_actual_complete_state_from_rank_moments

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.CompletedExpansion
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

open scoped BigOperators Classical

open scoped BigOperators Classical

namespace RayFourExpansion
open ActualEisensteinCubic ConcreteTraceCRT ActualEisensteinCoordinates QuadraticGaussRay
open FiniteRayExpansion

theorem rayCharacter_eq_of_mod_four (χ : RayCharacter) (a b : O) (h : (4 : O) ∣ a - b) :
    rayCharacter χ a = rayCharacter χ b := by
  unfold rayCharacter
  congr 1
  exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr h)

end RayFourExpansion

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.FrequencyCutoffs
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

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog primeProductNorm )
open ConcreteTraceCRT (eisEmbedding)

theorem mem_secondFrequencyCutoff (scale H : ℝ) (k : O)
    (hk : ‖eisEmbedding k‖^2 ≤ H/scale) : k ∈ secondFrequencyCutoff scale H := by
  apply ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le
  rw [eisEmbedding_norm_sq_eq_absNorm_span] at hk
  exact_mod_cast hk.trans (Nat.le_ceil (H/scale))

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels (columnLog jLabel b0Label )
open JointLogSeparation (tripleCoefficient)

end SecondPassArithmetic

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.CoordinateLaplacian
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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical
namespace CanonicalCoefficientClass

section
open ActualEisensteinCubic
open SecondPassArithmetic (rayMonoid conjugateRayMonoid rayMonoid_apply conjugateRayMonoid_apply
  FirstCoreIndex firstCoreTwist sideRayMonoid SecondRayIndex secondRayMinus secondRayPlus)
open RayFourExpansion (RayCharacter)

lemma IsBaseRayTwist.norm_le {base Ψ : ActualEisensteinCubic.O→*ℂ} (hΨ : IsBaseRayTwist base Ψ)
    (hbase : ∀x,‖base x‖≤1) (x : ActualEisensteinCubic.O) : ‖Ψ x‖≤1 := by
  rcases hΨ with rfl|⟨χ,rfl⟩
  · exact hbase x
  · rw [MonoidHom.mul_apply,norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (FiniteRayExpansion.norm_char_le_one χ _)).trans (hbase x)

end

open ActualEisensteinCubic
open ActualEisensteinCoordinates (eval coords eval_coords)
open ShortDraftLatticeCount (qNat qO_nonneg coords_eval)

end CanonicalCoefficientClass

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.GeneratorTransport
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem secondChildColumn_label_transfer (Ψ : Eis →* ℂ) (m a f k : Eis)
    (H : Finset ι → ℂ) (S : Finset ι) :
    secondChildColumn p hp hcop hg Ψ m (a*f) k H S =
      secondChildColumn p hp hcop hg Ψ m f (a^4*k) H S := by
  simp only [secondChildColumn, finiteSquarefreeRow, map_mul, map_pow,
    Finset.prod_mul_distrib, Finset.prod_pow, mul_pow]
  ring

omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRow_label_transfer (F : Finset ι) (Ψ : Eis →* ℂ)
    (m a f k : Eis) (slots : Finset σ) (lists : σ → Finset ι) (coeff : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg F Ψ m (a*f) k slots lists coeff W X =
      finiteCanonicalMarkedRow p hp hcop hg F Ψ m f (a^4*k) slots lists coeff W X := by
  simp only [finiteCanonicalMarkedRow,fixedChildRow,secondChildColumn_label_transfer]

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.ChildCutoff
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma mem_childFrequencyBall (a : Eis) (ha : a ≠ 0) (R : ℝ) (k : Eis) :
    k ∈ childFrequencyBall a R ↔ ‖eisEmbedding (a*k)‖^2 ≤ R := by
  have hn : 0 < ‖eisEmbedding a‖^2 := sq_pos_of_pos
    (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero ha))
  simp only [childFrequencyBall, Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_,h⟩⟩
  apply mem_secondFrequencyCutoff
  apply (le_div_iff₀ hn).mpr
  simpa only [map_mul, norm_mul, mul_pow, mul_comm] using h

lemma mem_nonzeroChildFrequencyBall (a : Eis) (ha : a ≠ 0) (R : ℝ) (k : Eis) :
    k ∈ nonzeroChildFrequencyBall a R ↔
      0 < ‖eisEmbedding (a*k)‖^2 ∧ ‖eisEmbedding (a*k)‖^2 ≤ R := by
  have hn : 0 < ‖eisEmbedding (a*k)‖^2 ↔ k ≠ 0 := by
    rw [sq_pos_iff, norm_ne_zero_iff]
    constructor
    · intro h hk; apply h; simp [hk]
    · intro hk; exact ConcreteTraceCRT.eisEmbedding_ne_zero (mul_ne_zero ha hk)
  simp only [nonzeroChildFrequencyBall, Finset.mem_erase,
    mem_childFrequencyBall a ha, hn]

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.ActualDepthBudget
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment

lemma actualDepth_pos (Mmax cutoff : ℝ) : 0<actualDepth Mmax cutoff := by
  exact Nat.succ_pos _

end SevenEighths.InverseMoment
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.CanonicalLongNormalization
namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
open InverseSecondFibers IdealMobiusDivisorSum InverseInitialClippedColumns
local notation "O"=>ActualEisensteinCubic.O

theorem child_ball_unit_mem (u:Oˣ)(R:ℝ)(k:O) :
    (u:O)*k∈nonzeroChildFrequencyBall 1 R ↔ k∈nonzeroChildFrequencyBall 1 R := by
  simp only [mem_nonzeroChildFrequencyBall 1 one_ne_zero,one_mul,
    GaussGeneratorTransport.norm_eisEmbedding_unit_mul]

theorem child_ball_unit_sum {A:Type*}[AddCommMonoid A](u:Oˣ)(R:ℝ)(f:O→A) :
    ∑k∈nonzeroChildFrequencyBall 1 R,f ((u:O)*k)=
      ∑k∈nonzeroChildFrequencyBall 1 R,f k := by
  apply Finset.sum_bij (fun k _=>(u:O)*k)
  · intro k hk
    exact (child_ball_unit_mem u R k).mpr hk
  · intro x hx y hy he
    exact mul_left_cancel₀ u.ne_zero he
  · intro y hy
    refine ⟨((u⁻¹:Oˣ):O)*y,(child_ball_unit_mem u⁻¹ R y).mpr hy,?_⟩
    rw [←mul_assoc,←Units.val_mul,mul_inv_cancel,Units.val_one,one_mul]
  · intros
    rfl

variable {ι σ:Type*}[DecidableEq ι]
  (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,goodLambda∉Ideal.span {p i})

theorem canonical_ball_generator_energy
    (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(I:Ideal O)(hI:primaryGenerator I≠0)
    (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(W:ℝ→ℂ)(X K:ℝ) :
    (∑k∈nonzeroChildFrequencyBall 1 K,
      ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator I) k slots lists a W X‖^2)=
    ∑k∈nonzeroChildFrequencyBall 1 K,
      ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (idealGenerator I) k slots lists a W X‖^2 := by
  obtain ⟨u,hu⟩:=generator_eq_unit_primary I (idealGenerator I) (span_idealGenerator I) hI
  let P:O→ℝ:=fun k=>
    ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator I) k slots lists a W X‖^2
  have hrot:=child_ball_unit_sum (u^4) K P
  have he (k:O):
      ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (idealGenerator I) k slots lists a W X‖^2=
      P (((u^4:Oˣ):O)*k) := by
    rw [hu,finiteCanonicalMarkedRow_label_transfer]
    rfl
  simp only [he]
  exact hrot.symm

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.Widths
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma actual_ideal_norm_pos (I : Ideal Eis) (hI : I ≠ 0) : 0 < (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.RecursionParameters
namespace OAI

noncomputable section

namespace SevenEighths.InverseMoment

theorem actual_step_parameters (F eta r ell epsChild:ℝ)
    (hF:0≤F)(heta:0<eta)(heta1:eta≤1)(hr:r≤F)(hell:ell≤F)(heps:0≤epsChild):
    0<firstPassEpsilon F eta ∧ 0<sourceMassEpsilon F eta ∧
    6*eta≤8*eta ∧
    sourceMassEpsilon F eta*(20*(3*F+16)+30)≤(8*eta)/4 ∧
    48*eta+eta+8*eta+epsChild+eta≤epsChild+58*eta ∧
    3*eta+firstPassEpsilon F eta*(5*ell+2*r+7*eta)≤epsChild+60*eta ∧
    (epsChild+58*eta)+(2*F+15*eta+eta)*firstPassEpsilon F eta+firstPassEpsilon F eta≤epsChild+60*eta :=by
  have hd:0<10*F+32:=by positivity
  have hm:0<20*(3*F+16)+30:=by positivity
  have he:0<firstPassEpsilon F eta:=div_pos heta hd
  have heq:firstPassEpsilon F eta*(10*F+32)=eta:=by unfold firstPassEpsilon;field_simp
  have heq':sourceMassEpsilon F eta*(20*(3*F+16)+30)=2*eta:=by unfold sourceMassEpsilon;field_simp
  refine ⟨he,div_pos (by positivity) hm,by linarith,by linarith,by ring_nf;linarith,?_,?_⟩
  · have hcap:5*ell+2*r+7*eta≤10*F+32:=by linarith
    have hh:=mul_le_mul_of_nonneg_left hcap he.le
    nlinarith
  · have hcap:2*F+15*eta+eta+1≤10*F+32:=by linarith
    have hh:=mul_le_mul_of_nonneg_left hcap he.le
    nlinarith

theorem actual_recursion_parameters (Mcap Fcap c eps:ℝ)(_hM:0≤Mcap)(_hF:0≤Fcap)(hc:0<c)(heps:0<eps):
    ∃cutoff eta:ℝ,0<cutoff ∧ 0<eta ∧ eta≤1 ∧ eta≤ cutoff/32 ∧
      cutoff≤(c/2)/200 ∧ eta≤(c/2)/100000 ∧
      let depth:=actualDepth Mcap (cutoff/2);
      (depth:ℝ)*7*eta≤ c/2 ∧ (depth:ℝ)*15*eta≤1 ∧
      (depth:ℝ)*100*eta≤eps/4 :=by
  let cutoff:=c/1000
  have hd:0<cutoff:=by dsimp[cutoff];positivity
  let depth:=actualDepth Mcap (cutoff/2)
  let D:ℝ:=(depth:ℝ)+1
  have hD:0<D:=by dsimp[D];positivity
  let eta:=min 1 (min (cutoff/32) (min (c/200000) (min (c/(28*D)) (min (1/(30*D)) (eps/(800*D))))))
  have he:0<eta:=by dsimp[eta];positivity
  have he1:eta≤1:=min_le_left _ _
  have he2:eta≤ cutoff/32:=(min_le_right _ _).trans (min_le_left _ _)
  have he3:eta≤ c/200000:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have he4:eta≤ c/(28*D):=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have he5:eta≤1/(30*D):=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have he6:eta≤eps/(800*D):=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  refine ⟨cutoff,eta,hd,he,he1,he2,by dsimp[cutoff];linarith,by linarith,?_⟩
  have h4:eta*(28*D)≤ c:=(le_div_iff₀ (by positivity)).mp he4
  have h5:eta*(30*D)≤1:=(le_div_iff₀ (by positivity)).mp he5
  have h6:eta*(800*D)≤eps:=(le_div_iff₀ (by positivity)).mp he6
  have hn:(depth:ℝ)*eta≤D*eta:=mul_le_mul_of_nonneg_right (by dsimp[D];linarith) he.le
  change (depth:ℝ)*7*eta≤ c/2 ∧ (depth:ℝ)*15*eta≤1 ∧ (depth:ℝ)*100*eta≤eps/4
  constructor <;> first | nlinarith | constructor <;> nlinarith

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.CanonicalCompleteBudget
namespace OAI

noncomputable section

namespace SevenEighths.InverseMoment

theorem actual_complete_step_cost (L eta epsChild:ℝ)(hL:0≤L)(heta:0<eta)
    (heta1:eta≤1)(heps:0≤epsChild):
    3*eta+firstPassEpsilon L eta*(2*L+7*eta)≤epsChild+60*eta ∧
    2*L*firstPassEpsilon L eta≤eta ∧
    (epsChild+60*eta)+2*L*firstPassEpsilon L eta+eta≤epsChild+62*eta := by
  have hd:0<10*L+32:=by positivity
  have hp:0<firstPassEpsilon L eta:=div_pos heta hd
  have he:firstPassEpsilon L eta*(10*L+32)=eta:=by unfold firstPassEpsilon;field_simp
  have hb:2*L+7*eta≤10*L+32:=by linarith
  have hc:=mul_le_mul_of_nonneg_left hb hp.le
  have hl:=mul_le_mul_of_nonneg_left (show 2*L≤10*L+32 by linarith) hp.le
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem actual_complete_height_merge (dshort dlong:ℕ)(Z F cstar loss Cs Cb A theta:ℝ)
    (hZ:1≤Z)(hcstar:0≤ cstar)(hloss:0≤loss)(hCs:0≤Cs)(hCb:0≤Cb)(hA:0≤A):
    Cs*(1+‖theta‖)^dshort*Z^(F-cstar/256)+
      Cb*(1+A)*(1+‖theta‖)^dlong*Z^(F+loss)≤
    (Cs+Cb)*(1+A)*(1+‖theta‖)^(max dshort dlong)*Z^(F+loss) := by
  have hp:1≤1+‖theta‖:=by linarith [norm_nonneg theta]
  have hshort:(1+‖theta‖)^dshort≤(1+‖theta‖)^(max dshort dlong):=
    pow_le_pow_right₀ hp (le_max_left _ _)
  have hlong:(1+‖theta‖)^dlong≤(1+‖theta‖)^(max dshort dlong):=
    pow_le_pow_right₀ hp (le_max_right _ _)
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hs:Z^(F-cstar/256)≤Z^(F+loss):=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hs':Cs*(1+‖theta‖)^dshort*Z^(F-cstar/256)≤
      Cs*(1+A)*(1+‖theta‖)^(max dshort dlong)*Z^(F+loss):=by
    calc
      _≤Cs*(1+‖theta‖)^(max dshort dlong)*Z^(F+loss):=by gcongr
      _≤_:=by
        have hh:Cs≤Cs*(1+A):=by nlinarith
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh (by positivity)) (by positivity)
  have hl':Cb*(1+A)*(1+‖theta‖)^dlong*Z^(F+loss)≤
      Cb*(1+A)*(1+‖theta‖)^(max dshort dlong)*Z^(F+loss):=by gcongr
  have hh:=add_le_add hs' hl'
  convert (preTransparency := .instances) hh using 1 ; ring

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.CanonicalCompleteNormalized
namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic InverseInitialClippedColumns
local notation "O"=>ActualEisensteinCubic.O

theorem normalizedColumnEnergy_eq_generator_sum {ι σ:Type*}[DecidableEq ι][DecidableEq σ]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (labels:Finset (Ideal O))(hlabels:∀I∈labels,primaryGenerator I≠0)
    (weight:Ideal O→ℝ)(W:ℝ→ℂ)(X Z F R:ℝ)(hZ:0<Z) :
    normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels
      (nonzeroChildFrequencyBall 1 R) weight W X Z F=
    Z^(-F)*(∑I∈labels,weight I*∑k∈nonzeroChildFrequencyBall 1 R,
      ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (idealGenerator I) k slots lists a W X‖^2) := by
  have hn:‖((Z^(-F/2):ℝ):ℂ)‖^2=Z^(-F) := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hZ _),
      ←Real.rpow_mul_natCast hZ.le]
    congr 1
    ring
  unfold normalizedColumnEnergy
  simp only [norm_mul,mul_pow,hn,←Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [canonical_ball_generator_energy p hp hcop hg pool Ψ m I (hlabels I hI)]
  ring

theorem outside_complete_normalized_energy {σ:Type*}[DecidableEq σ]
    (S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)
    (Ψ:O→*ℂ)(m:O)(slots:Finset σ)
    (lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
    (labels:Finset (Ideal O))(hlabels:∀I∈labels,Supported I)
    (weight:Ideal O→ℝ)(W:ℝ→ℂ)(X Z Fexp R:ℝ)(hZ:0<Z) :
    let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    Z^(-Fexp)*(∑I∈labels,weight I*∑k∈nonzeroChildFrequencyBall 1 R,
      ‖outsideCanonicalMarkedRow S D hbad Ψ m (idealGenerator I) k slots lists a W X‖^2)=
    normalizedColumnEnergy (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Ψ m slots lists a labels
      (nonzeroChildFrequencyBall 1 R) weight W X Z Fexp := by
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  exact (normalizedColumnEnergy_eq_generator_sum (poolPrimary F) (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Ψ m slots lists a labels
    (fun I hI=>supported_primaryGenerator_ne_zero I (hlabels I hI)) weight W X Z Fexp R hZ).symm

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.CanonicalRankMonotone
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CanonicalQuadraticSieve InverseInitialClippedColumns
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
variable (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
variable (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

omit [DecidableEq σ] in
theorem canonical_rank_negative (pool:Finset ι)(base:O→*ℂ)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:𝓢(ℝ,ℂ))(Z Mmax Fcap z c eps A:ℝ)(K degree:ℕ)(hM:Mmax<0):
    CanonicalRankMoments p hp hcop hg pool base slots lists a W Z Mmax Fcap z c eps A K degree :=by
  intro Ψ hΨ m hm N V M Qwidth hN hV hM0 hQ hMc
  exfalso
  linarith

omit [DecidableEq σ] in
theorem canonical_rank_restrict (pool:Finset ι)(base:O→*ℂ)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:𝓢(ℝ,ℂ))(Z M₁ M₂ F₁ F₂ z c₁ c₂ eps A:ℝ)(K degree:ℕ)
    (hM:M₁≤M₂)(hF:F₁≤F₂)(hc:c₂≤ c₁)
    (h:CanonicalRankMoments p hp hcop hg pool base slots lists a W Z M₂ F₂ z c₂ eps A K degree):
    CanonicalRankMoments p hp hcop hg pool base slots lists a W Z M₁ F₁ z c₁ eps A K degree :=by
  intro Ψ hΨ m hm N V M Qwidth hN hV hM0 hQ hMc hFc hmargin hnorm ss hss labels hlabels s
  have hmarg:CanonicalMargins (N+V) M Qwidth z c₂:=by
    unfold CanonicalMargins at *
    constructor <;> linarith [hmargin.1,hmargin.2]
  exact h Ψ hΨ m hm N V M Qwidth hN hV hM0 hQ (hMc.trans hM) (hFc.trans hF) hmarg hnorm ss hss labels hlabels s

omit [DecidableEq σ] in
theorem canonical_rank_height_constant (pool:Finset ι)(base:O→*ℂ)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:𝓢(ℝ,ℂ))(Z M F z c eps A B:ℝ)(K degree J:ℕ)
    (hZ:0<Z)(hA:0≤A)(hAB:A≤B)(hJ:degree≤J)
    (h:CanonicalRankMoments p hp hcop hg pool base slots lists a W Z M F z c eps A K degree):
    CanonicalRankMoments p hp hcop hg pool base slots lists a W Z M F z c eps B K J :=by
  intro Ψ hΨ m hm N V Mr Qwidth hN hV hM0 hQ hMc hFc hmargin hnorm ss hss labels hlabels s
  apply (h Ψ hΨ m hm N V Mr Qwidth hN hV hM0 hQ hMc hFc hmargin hnorm ss hss labels hlabels s).trans
  have hB:0≤B:=hA.trans hAB
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg hZ.le _)
  · exact pow_le_pow_right₀ (by linarith [norm_nonneg s]) (Nat.mul_le_mul_left 2 hJ)
  · positivity
  · positivity

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.CanonicalCompleteRankNormalized
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseMoment
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve CanonicalCubeSeparation FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstLabelCell InverseMomentFirstSecondHeightCost CompletedHeight
open InverseInitialClippedColumns FourierBridge JointLogSeparation InverseReflectedPhase InverseTerminalWidths InverseSecondFibers
local notation "O"=>ActualEisensteinCubic.O

theorem actual_complete_normalized_rank_step
    (lo hi:ℝ)(hlo:0<lo)(hhi:0≤hi)(W:ℝ→ℂ)
    (hsW:Function.support W⊆Set.Icc lo hi)(hW:ContDiff ℝ ∞ W)
    (Vlog:𝓢(ℝ,ℂ))(Alog:ℝ)(hbox:∀x,Vlog x≠0 → |x|≤Alog)
    (hone:∀x,|x|≤ columnWindowRadius lo hi → Vlog x=1)
    (L cstar eta tau saving em ed eps:ℝ)(hL:1≤L)(hcstar:0<cstar)(heta:0<eta)
    (heta1:eta≤1)(hetac:eta≤ cstar/100000)(htau:0<tau)(htau1:tau≤1)
    (hem:0<em)(hed:0<ed)(heps:0<eps)(K:ℕ):
    ∃(ω₁₁ ω₁₂ ω₂₁ ω₂₂:𝓢(ℝ,ℂ))(af₁ bf₁ af₂ bf₂ window bw:ℝ)(shortDegree:ℕ),
      0<af₁ ∧ af₁≤bf₁ ∧ 0<af₂ ∧ af₂≤bf₂ ∧
      HasCompactSupport (ω₁₁:ℝ→ℂ) ∧ HasCompactSupport (ω₁₂:ℝ→ℂ) ∧
      HasCompactSupport (ω₂₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂₂:ℝ→ℂ) ∧
      tsupport (ω₁₁:ℝ→ℂ)⊆Set.Icc af₁ bf₁ ∧ tsupport (ω₁₂:ℝ→ℂ)⊆Set.Icc af₁ bf₁ ∧
      tsupport (ω₂₁:ℝ→ℂ)⊆Set.Icc af₂ bf₂ ∧ tsupport (ω₂₂:ℝ→ℂ)⊆Set.Icc af₂ bf₂ ∧
      1≤bw ∧ Real.exp Alog≤bw ∧ bw=Real.exp window ∧
    ∀epsFirst epsSecond:ℝ,0<epsFirst → 0<epsSecond → ∀degree:ℕ,
    ∀(q:ℕ)(hq:q≠0),∃Cs Cb Z₀:ℝ,0<Cs ∧ 0≤Cb ∧ 1<Z₀ ∧
    ∀{σ:Type}[DecidableEq σ](m:O),m≠0 →
    ∀Z N V M z₀ margin cutoff pi epschild A loss lossFinal theta:ℝ,
      Z₀≤Z → 2≤Z → 2≤Z^eta → Real.exp 1≤Z^eta → 1≤eta*Real.log Z →
      0≤N → 0≤V → 0≤M → N+V≤L → M≤N+V → z₀≤L →
      hi≤Z^eta → Real.exp Alog≤Z^eta → Real.exp window≤Z^eta →
      0<cutoff → cutoff≤L → cutoff≤ cstar/200 → eta≤ cutoff/32 →
      (Ideal.absNorm (Ideal.span {m}):ℝ)≤Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤ margin →
      (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^(normWidth Z (Ideal.span {m})) →
      0≤pi → 6*eta≤pi → em*(20*(3*L+16)+30)≤pi/4 → ed*(20*(3*L+16)+30)≤pi/4 →
      0≤epschild → -saving≤48*eta+tau+pi+epschild+epsSecond →
      48*eta+tau+pi+epschild+epsSecond≤loss →
      3*eta+epsFirst*(2*L+7*eta)≤lossFinal →
      loss+(2*L+15*eta+tau)*epsFirst+epsFirst≤lossFinal → -saving≤lossFinal →
      0≤A →
    ∀labels:Finset (Ideal O),(∀I∈labels,Supported I ∧ Squarefree I ∧ (I.absNorm:ℝ)≤Z^V) →
    ∀D:ℕ,hi*Z^N≤D → ∀slots:Finset σ,slots.card≤K →
    ∀(lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))(H:σ→ℝ),
      (slots:Set σ).PairwiseDisjoint lists →
      (∀i∈slots,1≤H i) → (∀i∈slots,∀P∈lists i,(Ideal.absNorm P.val:ℝ)≤H i) → (∏i∈slots,H i)≤Z^z₀ →
    ∀(base Ψ:O→*ℂ),CanonicalCoefficientClass.IsBaseRayTwist base Ψ → (∀u,‖Ψ u‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ,
      (∀i∈slots,∀P∈lists i,‖a i P‖≤1) →
      let S:=reflectionExcludedPrimes q;
      let F:=InitialMeanSquare.outsideSquarefreeIdeals S D;
      let hF:=InitialMeanSquare.outsideSquarefree_admissible S D (reflectionExcludedPrimes_bad q);
      letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
      let _om:=radialFromLog Vlog (Vlog.smooth ⊤) Alog hbox;
      CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        (poolPrimary_good F hF) Finset.univ base slots lists a ω₁₁
        Z (M-3*(cutoff/2)/2) (N+V+15*eta) z₀ (margin-7*eta) epschild A K degree →
      CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        (poolPrimary_good F hF) Finset.univ base slots lists a ω₁₂
        Z (M-3*(cutoff/2)/2) (N+V+15*eta) z₀ (margin-7*eta) epschild A K degree →
      CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        (poolPrimary_good F hF) Finset.univ base slots lists a ω₂₁
        Z (M-3*(cutoff/2)/2) (N+V+15*eta) z₀ (margin-7*eta) epschild A K degree →
      CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        (poolPrimary_good F hF) Finset.univ base slots lists a ω₂₂
        Z (M-3*(cutoff/2)/2) (N+V+15*eta) z₀ (margin-7*eta) epschild A K degree →
      normalizedColumnEnergy (poolPrimary F) (poolPrimary_ne_zero F hF)
        (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Ψ m slots lists a labels
        (nonzeroChildFrequencyBall 1 (Z^M)) (secondLabelWeight K) (normTwistedSource W theta)
        (Z^N) Z (N+V)≤
      Cs*(1+‖theta‖)^shortDegree*Z^(N+V-cstar/256)+
      Cb*(1+A)*(1+‖theta‖)^(2*(InverseClippingProfiles.momentOrder (firstDegree degree)+(volume:Measure ℝ).integrablePower))*
        Z^(N+V+lossFinal+2*L*epsFirst+eps) := by
  obtain ⟨w11,w12,w21,w22,af1,bf1,af2,bf2,window,bw,ds,ha1,hab1,ha2,hab2,
    hw11,hw12,hw21,hw22,hs11,hs12,hs21,hs22,hbw,hbA,hbexp,hstep⟩:=
    actual_complete_state_from_rank_moments lo hi hlo hhi W hsW hW Vlog Alog hbox hone
      L cstar eta tau saving em ed eps hL hcstar heta heta1 hetac htau htau1 hem hed heps K
  refine ⟨w11,w12,w21,w22,af1,bf1,af2,bf2,window,bw,ds,ha1,hab1,ha2,hab2,
    hw11,hw12,hw21,hw22,hs11,hs12,hs21,hs22,hbw,hbA,hbexp,?_⟩
  intro epsFirst epsSecond heF heS degree q hq
  obtain ⟨Cs,Cb,Z₀,hCs,hCb,hZ₀,hstep⟩:=hstep epsFirst epsSecond heF heS degree q hq
  refine ⟨Cs,Cb,Z₀,hCs,hCb,hZ₀,?_⟩
  intro σ _ m hm Z N V M z₀ margin cutoff pi epschild A loss lossFinal theta hZ hZ2 h2 hExp hlog
    hN hV hM hFcap hMF hzcap hbZ hAZ hwin hcut hcutL hcutc hsmall hmN hmargin hreserve hpuncture
    hpi hpieta hemc hedc hechild hsave hloss hprincipal hretained htail hA
    labels hlabels D hD slots hcard lists H hdis hH1 hH hprod base Ψ hbase hΨ hperiod a ha
  dsimp only
  intro h11 h12 h21 h22
  have hh:=hstep m hm Z N V M z₀ margin cutoff pi epschild A loss lossFinal theta hZ hZ2 h2 hExp hlog
    hN hV hM hFcap hMF hzcap hbZ hAZ hwin hcut hcutL hcutc hsmall hmN hmargin hreserve hpuncture
    hpi hpieta hemc hedc hechild hsave hloss hprincipal hretained htail hA
    labels hlabels D hD slots hcard lists H hdis hH1 hH hprod base Ψ hbase hΨ hperiod a ha h11 h12 h21 h22
  rw [outside_complete_normalized_energy (reflectionExcludedPrimes q) D (reflectionExcludedPrimes_bad q)
    Ψ m slots lists a labels (fun I hI=>(hlabels I hI).1) (secondLabelWeight K)
    (normTwistedSource W theta) (Z^N) Z (N+V) (Z^M) (by linarith)] at hh
  exact hh

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.CanonicalRankPuncture
namespace OAI

noncomputable section

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic InverseTerminalWidths
local notation "O"=>ActualEisensteinCubic.O

theorem actual_rank_parent_puncture (m:O)(hm:m≠0)(Z:ℝ)(hZ:1<Z):
    (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^(normWidth Z (Ideal.span {m})) :=by
  have hi:(Ideal.span {m}:Ideal O)≠0:=Ideal.span_singleton_eq_bot.not.mpr hm
  have hn:0<(Ideal.absNorm (Ideal.span {m}:Ideal O):ℝ):=actual_ideal_norm_pos _ hi
  have hle:Ideal.absNorm (Ideal.span {m}:Ideal O).radical≤Ideal.absNorm (Ideal.span {m}:Ideal O):=
    Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hi))
      (Ideal.absNorm_dvd_absNorm_of_le Ideal.le_radical)
  unfold normWidth
  rw [Real.rpow_logb (by linarith:0<Z) (ne_of_gt hZ) hn]
  exact_mod_cast hle

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.CanonicalRankExistenceData
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion InverseInitialClippedColumns InverseReflectedPhase
local notation "O"=>ActualEisensteinCubic.O

theorem rank_energy_exists_zero (L cstar cutoff eta:ℝ)(hcut:0<cutoff)(K:ℕ)(W:𝓢(ℝ,ℂ)):
    RankEnergyExists 0 L cstar cutoff eta K W :=by
  refine ⟨0,1,le_rfl,?_⟩
  intro q hq
  refine ⟨1,2,by norm_num,by norm_num,?_⟩
  intro Z hZ D hD σ _ slots hslots lists H a hdis hH hP ha z hz hprod base hb hp
  dsimp only [CompletePoolRankMoments]
  let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) D (reflectionExcludedPrimes_bad q)
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance
  apply canonical_rank_negative
  simp only [rankRowCap,Nat.cast_zero]
  linarith

theorem actual_rank_successor_caps (n:ℕ)(L cstar cutoff eta M F c:ℝ)
    (hM:M≤ rankRowCap (n+1) cutoff)(hF:F≤ rankTotalCap (n+1) L eta)
    (hc:rankMargin (n+1) cstar eta≤ c):
    M-3*cutoff/4≤ rankRowCap n cutoff ∧ F+15*eta≤ rankTotalCap n L eta ∧
      rankMargin n cstar eta≤ c-7*eta :=by
  unfold rankRowCap rankTotalCap rankMargin at *
  push_cast at *
  constructor <;> first | linarith | constructor <;> linarith

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.CanonicalRankEnergyMonotone
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CanonicalQuadraticSieve InverseInitialClippedColumns
local notation "O"=>ActualEisensteinCubic.O

theorem canonical_rank_loss_le {ι σ:Type}[DecidableEq ι][DecidableEq σ]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(base:O→*ℂ)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:𝓢(ℝ,ℂ))(Z M F z c eps eps' A:ℝ)(K degree:ℕ)
    (hZ:1≤Z)(hA:0≤A)(he:eps≤eps')
    (h:CanonicalRankMoments p hp hcop hg pool base slots lists a W Z M F z c eps A K degree):
    CanonicalRankMoments p hp hcop hg pool base slots lists a W Z M F z c eps' A K degree :=by
  intro Ψ hΨ m hm N V Mr Q hN hV hM hQ hMc hFc hmargin hnorm ss hss labels hlabels s
  apply (h Ψ hΨ m hm N V Mr Q hN hV hM hQ hMc hFc hmargin hnorm ss hss labels hlabels s).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) hA

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.CanonicalEnergyExistenceData
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion InverseReflectedPhase
local notation "O"=>ActualEisensteinCubic.O

theorem canonical_energy_of_rank (n:ℕ)(L cstar cutoff eta Mcap Fcap c eps:ℝ)(K:ℕ)(W:𝓢(ℝ,ℂ))
    (hM:Mcap≤ rankRowCap n cutoff)(hF:Fcap≤ rankTotalCap n L eta)
    (hc:rankMargin n cstar eta≤ c)(he:rankLoss n eta≤eps)
    (h:RankEnergyExists n L cstar cutoff eta K W):
    CanonicalEnergyExists Mcap Fcap c eps L K W :=by
  obtain ⟨degree,B,hB,h⟩:=h
  refine ⟨degree,B,hB,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,h⟩:=h q hq
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ D hD σ _ slots hslots lists H a hdis hH hP ha z hz hprod base hb hp
  have hmom:=h Z hZ D hD slots hslots lists H a hdis hH hP ha z hz hprod base hb hp
  dsimp only [CompletePoolRankMoments] at hmom ⊢
  let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D
  have hFa:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) D (reflectionExcludedPrimes_bad q)
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  apply canonical_rank_loss_le (poolPrimary F) (poolPrimary_ne_zero F hFa) (poolPrimary_coprime F hFa)
    (poolPrimary_good F hFa) Finset.univ base slots lists a W Z Mcap Fcap z c (rankLoss n eta) eps C K degree
    (by linarith) hC.le he
  exact canonical_rank_restrict (poolPrimary F) (poolPrimary_ne_zero F hFa) (poolPrimary_coprime F hFa)
    (poolPrimary_good F hFa) Finset.univ base slots lists a W Z Mcap (rankRowCap n cutoff)
    Fcap (rankTotalCap n L eta) z c (rankMargin n cstar eta) (rankLoss n eta) C K degree hM hF hc hmom

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.CanonicalRankDepthParameters
namespace OAI

noncomputable section

namespace SevenEighths.InverseMoment

theorem actual_rank_depth_covers (Mmax cutoff:ℝ)(hcut:0<cutoff):
    Mmax≤ rankRowCap (actualDepth Mmax (cutoff/2)) cutoff := by
  have hceil:=Nat.le_ceil (2*Mmax/(3*(cutoff/2)))
  have hscaled:2*Mmax≤(⌈2*Mmax/(3*(cutoff/2))⌉₊:ℝ)*(3*(cutoff/2)):=
    (div_le_iff₀ (by positivity:0<3*(cutoff/2))).mp hceil
  unfold rankRowCap actualDepth
  push_cast
  nlinarith

theorem actual_rank_depth_parameters (Mmax Fmax c eps:ℝ)
    (hM:0≤Mmax)(hF:0≤Fmax)(hc:0<c)(heps:0<eps):
    ∃cutoff eta:ℝ,0<cutoff ∧ 0<eta ∧ eta≤1 ∧ eta≤ cutoff/32 ∧
      cutoff≤Fmax+1 ∧ cutoff≤ c/200 ∧ eta≤ c/100000 ∧
      let n:=actualDepth Mmax (cutoff/2);
      0<n ∧ Mmax≤ rankRowCap n cutoff ∧
      ∀k:ℕ,k≤n→Fmax≤ rankTotalCap k (Fmax+1) eta ∧
        c/2≤ rankMargin k c eta ∧ rankMargin k c eta≤ c ∧
        0≤ rankLoss k eta ∧ rankLoss k eta≤eps/4 := by
  let csmall:=min c 1
  have hcs:0<csmall:=lt_min hc (by norm_num)
  have hcc:csmall≤ c:=min_le_left _ _
  have hc1:csmall≤1:=min_le_right _ _
  obtain ⟨cutoff,eta,hcut,heta,heta1,hetacut,hcutc,hetac,hbudgets⟩:=
    actual_recursion_parameters Mmax Fmax csmall eps hM hF hcs heps
  dsimp only at hbudgets
  refine ⟨cutoff,eta,hcut,heta,heta1,hetacut,by linarith,by linarith,by linarith,?_⟩
  dsimp only
  refine ⟨actualDepth_pos _ _,actual_rank_depth_covers Mmax cutoff hcut,?_⟩
  intro k hk
  have hk':(k:ℝ)≤(actualDepth Mmax (cutoff/2):ℝ):=by exact_mod_cast hk
  have hmono:=mul_le_mul_of_nonneg_right hk' heta.le
  have hk0:0≤(k:ℝ):=Nat.cast_nonneg _
  have hkE:0≤(k:ℝ)*eta:=mul_nonneg hk0 heta.le
  rcases hbudgets with ⟨hmargin,hsize,hloss⟩
  unfold rankTotalCap rankMargin rankLoss
  refine ⟨?_,?_,?_,?_,?_⟩ <;> nlinarith

theorem actual_rank_top_parameters (Mmax Fmax c eps:ℝ)
    (hM:0≤Mmax)(hF:0≤Fmax)(hc:0<c)(heps:0<eps):
    ∃(n:ℕ)(cutoff eta:ℝ),n=actualDepth Mmax (cutoff/2) ∧
      0<n ∧ 0<cutoff ∧ 0<eta ∧ eta≤1 ∧ eta≤ cutoff/32 ∧
      cutoff≤Fmax+1 ∧ cutoff≤ c/200 ∧ eta≤ c/100000 ∧
      Mmax≤ rankRowCap n cutoff ∧ Fmax≤ rankTotalCap n (Fmax+1) eta ∧
      c/2≤ rankMargin n c eta ∧ rankMargin n c eta≤ c ∧
      0≤ rankLoss n eta ∧ rankLoss n eta<eps := by
  obtain ⟨cutoff,eta,hcut,heta,heta1,hetacut,hcutL,hcutc,hetac,hn,hrow,hall⟩:=
    actual_rank_depth_parameters Mmax Fmax c eps hM hF hc heps
  have htop:=hall (actualDepth Mmax (cutoff/2)) le_rfl
  refine ⟨actualDepth Mmax (cutoff/2),cutoff,eta,rfl,hn,hcut,heta,heta1,hetacut,
    hcutL,hcutc,hetac,hrow,htop.1,htop.2.1,htop.2.2.1,htop.2.2.2.1,?_⟩
  linarith [htop.2.2.2.2]

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.CanonicalRankFamilyGates
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CanonicalCoefficientClass InverseTerminalWidths
open ConcretePrimeRowBridge CompletedGauss
local notation "O"=>ActualEisensteinCubic.O

theorem actual_rank_family_period (q:ℕ)(base Ψ:O→*ℂ)
    (hbase:FactorsModulo (fixedBaseConductor q) base)
    (hΨ:IsBaseRayTwist base Ψ):
    FactorsModulo (fixedBaseConductor q) Ψ := by
  intro x y hxy
  rcases hΨ with rfl|⟨χ,rfl⟩
  · exact hbase x y hxy
  · simp only [MonoidHom.mul_apply]
    rw [hbase x y hxy]
    congr 1
    exact RayFourExpansion.rayCharacter_eq_of_mod_four χ x y
      (Ideal.mem_span_singleton.mp (Ideal.mul_le_right hxy))

theorem actual_rank_family_gates (q:ℕ)(base:O→*ℂ)
    (hbase:∀x,‖base x‖≤1)(hperiod:FactorsModulo (fixedBaseConductor q) base):
    ∀Ψ:O→*ℂ,IsBaseRayTwist base Ψ→
      (∀x,‖Ψ x‖≤1) ∧ FactorsModulo (fixedBaseConductor q) Ψ := by
  intro Ψ hΨ
  exact ⟨hΨ.norm_le hbase,actual_rank_family_period q base Ψ hperiod hΨ⟩

theorem actual_rank_norm_width (m:O)(Z Q:ℝ)(hZ:1<Z)
    (hn:‖ConcreteTraceCRT.eisEmbedding m‖^2=Z^Q):
    normWidth Z (Ideal.span {m})=Q := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span] at hn
  rw [normWidth,hn,Real.logb_rpow (zero_lt_one.trans hZ) (ne_of_gt hZ)]

theorem actual_rank_state_gates (m:O)(hm:m≠0)(Z N V M Q z c L:ℝ)
    (hZ:1<Z)(hN:0≤N)(hV:0≤V)(hM:0≤M)(hQ:0≤Q)(hz:0≤z)(hc:0≤ c)
    (hcap:N+V≤L)(hmargin:CanonicalMargins (N+V) M Q z c)
    (hn:‖ConcreteTraceCRT.eisEmbedding m‖^2=Z^Q):
    N≤L ∧ V≤L ∧ M≤N+V ∧ Q≤L ∧ z≤L ∧
      normWidth Z (Ideal.span {m})=Q ∧
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z c ∧
      (Ideal.absNorm (Ideal.span {m}:Ideal O):ℝ)≤Z^L ∧
      (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^Q := by
  have hfirst:=hmargin.1
  have hQcap:Q≤L:=by linarith
  have he:=actual_rank_norm_width m Z Q hZ hn
  refine ⟨by linarith,by linarith,by linarith,hQcap,by linarith,he,?_,?_,?_⟩
  · rwa [he]
  · rw [eisEmbedding_norm_sq_eq_absNorm_span] at hn
    rw [hn]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le hQcap
  · simpa only [he] using actual_rank_parent_puncture m hm Z hZ

theorem canonical_rank_subslots {ι σ:Type}[DecidableEq ι][DecidableEq σ]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(base:O→*ℂ)(slots subslots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:𝓢(ℝ,ℂ))(Z M F z c eps A:ℝ)(K degree:ℕ)(hsub:subslots⊆slots)
    (h:CanonicalRankMoments p hp hcop hg pool base slots lists a W Z M F z c eps A K degree):
    CanonicalRankMoments p hp hcop hg pool base subslots lists a W Z M F z c eps A K degree := by
  intro Ψ hΨ m hm N V Mr Qwidth hN hV hM hQ hMc hFc hmargin hnorm ss hss labels hlabels s
  exact h Ψ hΨ m hm N V Mr Qwidth hN hV hM hQ hMc hFc hmargin hnorm ss
    (hss.trans hsub) labels hlabels s

theorem canonical_rank_subslot_product {σ:Type*}[DecidableEq σ]
    (slots subslots:Finset σ)(H:σ→ℝ)(hsub:subslots⊆slots)
    (hH:∀i∈slots,1≤H i):
    (∏i∈subslots,H i)≤∏i∈slots,H i :=
  Finset.prod_le_prod_of_subset_of_one_le hsub
    (fun i hi=>(zero_le_one: (0:ℝ)≤1).trans (hH i (hsub hi)))
    (fun i hi _=>hH i hi)

theorem canonical_rank_subslot_cap {σ:Type*}[DecidableEq σ]
    (slots subslots:Finset σ)(H:σ→ℝ)(Z z:ℝ)(hsub:subslots⊆slots)
    (hH:∀i∈slots,1≤H i)(hcap:(∏i∈slots,H i)≤Z^z):
    (∏i∈subslots,H i)≤Z^z :=
  (canonical_rank_subslot_product slots subslots H hsub hH).trans hcap

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.CanonicalRankExistenceSuccessor
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseMoment
open MeasureTheory ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion InverseInitialClippedColumns InverseReflectedPhase InverseTerminalWidths
open CanonicalCubeSeparation CompletedHeight InverseMomentFirstSecondHeightCost
local notation "O"=>ActualEisensteinCubic.O

theorem rank_energy_exists_succ_of_reference
    (n:ℕ)(L cstar cutoff eta:ℝ)(K:ℕ)
    (hL:1≤L)(hcstar:0<cstar)(hcut:0<cutoff)(hcutL:cutoff≤L)
    (hcutc:cutoff≤ cstar/200)(heta:0<eta)(heta1:eta≤1)
    (hetac:eta≤ cstar/100000)(hetad:eta≤ cutoff/32)
    (hIH:∀(W:𝓢(ℝ,ℂ))(lo hi:ℝ),0<lo→0≤hi→
      Function.support (W:ℝ→ℂ)⊆Set.Icc lo hi→RankEnergyExists n L cstar cutoff eta K W)
    (W:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hhi:0≤hi)
    (hsW:Function.support (W:ℝ→ℂ)⊆Set.Icc lo hi)
    (Vlog:𝓢(ℝ,ℂ))(Alog:ℝ)(hbox:∀x,Vlog x≠0→|x|≤Alog)
    (hone:∀x,|x|≤ columnWindowRadius lo hi→Vlog x=1)
    (hlarge:∀window:ℝ,∃Zt:ℝ,1<Zt ∧ ∀Z:ℝ,Zt≤Z→
      2≤Z ∧ 2≤Z^eta ∧ Real.exp 1≤Z^eta ∧ 1≤eta*Real.log Z ∧
      hi≤Z^eta ∧ Real.exp Alog≤Z^eta ∧ Real.exp window≤Z^eta):
    RankEnergyExists (n+1) L cstar cutoff eta K W :=by
  have hL0:0≤L:=by linarith
  have heF:0<firstPassEpsilon L eta:=by unfold firstPassEpsilon;positivity
  have hem:0<sourceMassEpsilon L eta:=by unfold sourceMassEpsilon;positivity
  obtain ⟨w11,w12,w21,w22,af1,bf1,af2,bf2,window,bw,ds,ha1,hab1,ha2,hab2,
    hw11,hw12,hw21,hw22,hs11,hs12,hs21,hs22,hbw,hbA,hbexp,hstep⟩:=
    actual_complete_normalized_rank_step lo hi hlo hhi W hsW (W.smooth ⊤) Vlog Alog hbox hone
      L cstar eta eta 1 (sourceMassEpsilon L eta) (sourceMassEpsilon L eta) eta
      hL hcstar heta heta1 hetac heta heta1 hem hem heta K
  obtain ⟨J11,B11,hB11,ih11⟩:=hIH w11 af1 bf1 ha1 (by linarith) (subset_closure.trans hs11)
  obtain ⟨J12,B12,hB12,ih12⟩:=hIH w12 af1 bf1 ha1 (by linarith) (subset_closure.trans hs12)
  obtain ⟨J21,B21,hB21,ih21⟩:=hIH w21 af2 bf2 ha2 (by linarith) (subset_closure.trans hs21)
  obtain ⟨J22,B22,hB22,ih22⟩:=hIH w22 af2 bf2 ha2 (by linarith) (subset_closure.trans hs22)
  let J:=J11+J12+J21+J22
  let dl:=2*(InverseClippingProfiles.momentOrder (firstDegree J)+(volume:Measure ℝ).integrablePower)
  let Jout:=max ds dl
  let B:=1+hi+B11+B12+B21+B22
  have hB:1≤B:=by dsimp [B];linarith
  have hb0:0≤B:=by linarith
  have hhiB:hi≤B:=by dsimp [B];linarith
  have hBB11:B11≤B:=by dsimp [B];linarith
  have hBB12:B12≤B:=by dsimp [B];linarith
  have hBB21:B21≤B:=by dsimp [B];linarith
  have hBB22:B22≤B:=by dsimp [B];linarith
  have hj11:J11≤J:=by dsimp [J];omega
  have hj12:J12≤J:=by dsimp [J];omega
  have hj21:J21≤J:=by dsimp [J];omega
  have hj22:J22≤J:=by dsimp [J];omega
  obtain ⟨Zt,hZt,hlarge⟩:=hlarge window
  refine ⟨Jout,B,hB,?_⟩
  intro q hq
  obtain ⟨C11,Z11,hC11,hZ11,ih11⟩:=ih11 q hq
  obtain ⟨C12,Z12,hC12,hZ12,ih12⟩:=ih12 q hq
  obtain ⟨C21,Z21,hC21,hZ21,ih21⟩:=ih21 q hq
  obtain ⟨C22,Z22,hC22,hZ22,ih22⟩:=ih22 q hq
  obtain ⟨Cs,Cb,Zs,hCs,hCb,hZs,hstep⟩:=hstep (firstPassEpsilon L eta) eta heF heta J q hq
  let A:=C11+C12+C21+C22
  have hA:0≤A:=by dsimp [A];linarith
  have hCA11:C11≤A:=by dsimp [A];linarith
  have hCA12:C12≤A:=by dsimp [A];linarith
  have hCA21:C21≤A:=by dsimp [A];linarith
  have hCA22:C22≤A:=by dsimp [A];linarith
  let C:=(Cs+Cb)*(1+A)
  let Z₀:=Zs+Zt+Z11+Z12+Z21+Z22
  have hC:0<C:=by dsimp [C];positivity
  have hZ₀:1<Z₀:=by dsimp [Z₀];linarith
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ D hD σ _ slots hslots lists H a hdis hH hP ha z hz hprod base hbase hperiod
  have hZs':Zs≤Z:=by dsimp [Z₀] at hZ;linarith
  have hZt':Zt≤Z:=by dsimp [Z₀] at hZ;linarith
  have hZ11':Z11≤Z:=by dsimp [Z₀] at hZ;linarith
  have hZ12':Z12≤Z:=by dsimp [Z₀] at hZ;linarith
  have hZ21':Z21≤Z:=by dsimp [Z₀] at hZ;linarith
  have hZ22':Z22≤Z:=by dsimp [Z₀] at hZ;linarith
  obtain ⟨hZ2,h2,hExp,hlog,hhiZ,hAZ,hwin⟩:=hlarge Z hZt'
  have hZ1:1<Z:=by linarith
  have hZ0:0<Z:=by linarith
  have hD11:B11*Z^L≤D:=(mul_le_mul_of_nonneg_right hBB11 (Real.rpow_nonneg hZ0.le _)).trans hD
  have hD12:B12*Z^L≤D:=(mul_le_mul_of_nonneg_right hBB12 (Real.rpow_nonneg hZ0.le _)).trans hD
  have hD21:B21*Z^L≤D:=(mul_le_mul_of_nonneg_right hBB21 (Real.rpow_nonneg hZ0.le _)).trans hD
  have hD22:B22*Z^L≤D:=(mul_le_mul_of_nonneg_right hBB22 (Real.rpow_nonneg hZ0.le _)).trans hD
  have m11:=ih11 Z hZ11' D hD11 slots hslots lists H a hdis hH hP ha z hz hprod base hbase hperiod
  have m12:=ih12 Z hZ12' D hD12 slots hslots lists H a hdis hH hP ha z hz hprod base hbase hperiod
  have m21:=ih21 Z hZ21' D hD21 slots hslots lists H a hdis hH hP ha z hz hprod base hbase hperiod
  have m22:=ih22 Z hZ22' D hD22 slots hslots lists H a hdis hH hP ha z hz hprod base hbase hperiod
  let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) D (reflectionExcludedPrimes_bad q)
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only [CompletePoolRankMoments] at m11 m12 m21 m22 ⊢
  intro Ψ hΨ m hm N V M Qwidth hN hV hM hQ hMc hFc hmargin hnorm ss hss labels hlabels theta
  have hcap:N+V≤L:=by
    unfold rankTotalCap at hFc
    have hh:0≤15*((n+1:ℕ):ℝ)*eta:=by positivity
    linarith
  have hcm:0≤ rankMargin (n+1) cstar eta:=by unfold rankMargin;positivity
  obtain ⟨hNL,hVL,hMF,hQL,hzL,hwidth,hmargin',hmL,hpuncture⟩:=
    actual_rank_state_gates m hm Z N V M Qwidth z (rankMargin (n+1) cstar eta) L
      hZ1 hN hV hM hQ hz hcm hcap hmargin hnorm
  obtain ⟨hΨnorm,hΨperiod⟩:=actual_rank_family_gates q base hbase hperiod Ψ hΨ
  have hDparent:hi*Z^N≤D:=by
    calc
      _≤B*Z^L:=mul_le_mul hhiB (Real.rpow_le_rpow_of_exponent_le hZ1.le hNL)
        (Real.rpow_nonneg hZ0.le _) hb0
      _≤D:=hD
  have hsscard:ss.card≤K:=(Finset.card_le_card hss).trans hslots
  have hssdis:(ss:Set σ).PairwiseDisjoint lists:=by
    intro i hi j hj hij
    exact hdis (hss hi) (hss hj) hij
  have hssH:∀i∈ss,1≤H i:=fun i hi=>hH i (hss hi)
  have hssP:∀i∈ss,∀P∈lists i,(Ideal.absNorm P.val:ℝ)≤H i:=fun i hi=>hP i (hss hi)
  have hssa:∀i∈ss,∀P∈lists i,‖a i P‖≤1:=fun i hi=>ha i (hss hi)
  have hssprod:(∏i∈ss,H i)≤Z^z:=canonical_rank_subslot_cap slots ss H Z z hss hH hprod
  obtain ⟨hsmallM,hsmallF,hsmallc⟩:=actual_rank_successor_caps n L cstar cutoff eta M (N+V)
    (rankMargin (n+1) cstar eta) hMc hFc le_rfl
  have lift (w:𝓢(ℝ,ℂ))(Cw:ℝ)(Jw:ℕ)(hCw:0≤Cw)(hCwA:Cw≤A)(hJw:Jw≤J)
      (mw:CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        (poolPrimary_good F hF) Finset.univ base slots lists a w Z (rankRowCap n cutoff)
        (rankTotalCap n L eta) z (rankMargin n cstar eta) (rankLoss n eta) Cw K Jw):
      CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        (poolPrimary_good F hF) Finset.univ base ss lists a w Z (M-3*(cutoff/2)/2)
        (N+V+15*eta) z (rankMargin (n+1) cstar eta-7*eta) (rankLoss n eta) A K J:=by
    apply canonical_rank_subslots (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
      (poolPrimary_good F hF) Finset.univ base slots ss lists a w Z _ _ z _ _ A K J hss
    apply canonical_rank_restrict (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
      (poolPrimary_good F hF) Finset.univ base slots lists a w Z
      (M-3*(cutoff/2)/2) (rankRowCap n cutoff) (N+V+15*eta) (rankTotalCap n L eta)
      z (rankMargin (n+1) cstar eta-7*eta) (rankMargin n cstar eta) (rankLoss n eta) A K J
      (by linarith) hsmallF hsmallc
    exact canonical_rank_height_constant (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
      (poolPrimary_good F hF) Finset.univ base slots lists a w Z _ _ z _ _ Cw A K Jw J
      hZ0 hCw hCwA hJw mw
  have hechild:0≤ rankLoss n eta:=by unfold rankLoss;positivity
  obtain ⟨_,_,hpieta,hmass,hret,hprincipal0,hcost⟩:=actual_step_parameters L eta 0 0 (rankLoss n eta)
    hL0 heta heta1 (by linarith) (by linarith) hechild
  obtain ⟨hprincipal,hFirst,hFinal⟩:=actual_complete_step_cost L eta (rankLoss n eta) hL0 heta heta1 hechild
  have hreserve:cstar/2≤ rankMargin (n+1) cstar eta:=by
    unfold rankMargin
    exact le_add_of_nonneg_right (by positivity)
  have hbound:=hstep m hm Z N V M z (rankMargin (n+1) cstar eta) cutoff (8*eta)
    (rankLoss n eta) A (rankLoss n eta+58*eta) (rankLoss n eta+60*eta) theta
    hZs' hZ2 h2 hExp hlog hN hV hM hcap hMF hzL hhiZ hAZ hwin hcut hcutL hcutc hetad hmL hmargin'
    hreserve (by simpa only [hwidth] using hpuncture) (by positivity) hpieta hmass hmass hechild
    (by linarith) hret hprincipal hcost (by linarith) hA
    labels (fun I hI=>⟨⟨(hlabels I hI).1.1,(hlabels I hI).1.2.2⟩,(hlabels I hI).1.2.1,(hlabels I hI).2⟩)
    D hDparent ss hsscard lists H hssdis hssH hssP hssprod base Ψ hΨ hΨnorm hΨperiod a hssa
    (lift w11 C11 J11 hC11.le hCA11 hj11 m11) (lift w12 C12 J12 hC12.le hCA12 hj12 m12)
    (lift w21 C21 J21 hC21.le hCA21 hj21 m21) (lift w22 C22 J22 hC22.le hCA22 hj22 m22)
  have hnextLoss:rankLoss n eta+62*eta=rankLoss (n+1) eta:=by unfold rankLoss;push_cast;ring
  have hlongexp:(rankLoss n eta+60*eta)+2*L*firstPassEpsilon L eta+eta≤ rankLoss (n+1) eta:=by
    simpa only [hnextLoss] using hFinal
  have hloss0:0≤ rankLoss (n+1) eta:=by unfold rankLoss;positivity
  have hlong:Cb*(1+A)*(1+‖theta‖)^dl*
      Z^(N+V+(rankLoss n eta+60*eta)+2*L*firstPassEpsilon L eta+eta)≤
      Cb*(1+A)*(1+‖theta‖)^dl*Z^(N+V+rankLoss (n+1) eta):=by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le hZ1.le
    linarith
  have hh:=hbound.trans (add_le_add le_rfl hlong)
  have hmrg:=actual_complete_height_merge ds dl Z (N+V) cstar (rankLoss (n+1) eta) Cs Cb A theta
    hZ1.le hcstar.le hloss0 hCs.le hCb hA
  have hpow:(1+‖theta‖)^Jout≤(1+‖theta‖)^(2*Jout):=
    pow_le_pow_right₀ (by linarith [norm_nonneg theta]) (by omega)
  have hf:childLogTest W theta=normTwistedSource W theta:=by
    funext y
    simp only [childLogTest,normTwistedSource,mul_comm]
  rw [hf]
  apply (hh.trans hmrg).trans
  dsimp only [C,Jout]
  have hx:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow (show 0≤(Cs+Cb)*(1+A) by positivity))
    (Real.rpow_nonneg hZ0.le (N+V+rankLoss (n+1) eta))
  convert (preTransparency := .instances) hx using 1 ; ring

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.CanonicalRankExistenceInduction
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMoment
open CanonicalCubeSeparation

theorem rank_energy_exists_all_of_references
    (href:RankReferenceCutoffs)(hthreshold:RankReferenceThresholds)
    (L cstar cutoff eta:ℝ)(K:ℕ)
    (hL:1≤L)(hcstar:0<cstar)(hcut:0<cutoff)(hcutL:cutoff≤L)
    (hcutc:cutoff≤ cstar/200)(heta:0<eta)(heta1:eta≤1)
    (hetac:eta≤ cstar/100000)(hetad:eta≤ cutoff/32):
    ∀n:ℕ,∀(W:𝓢(ℝ,ℂ))(lo hi:ℝ),0<lo→0≤hi→
      Function.support (W:ℝ→ℂ)⊆Set.Icc lo hi→RankEnergyExists n L cstar cutoff eta K W :=by
  intro n
  induction n with
  | zero =>
      intro W lo hi hlo hhi hsW
      exact rank_energy_exists_zero L cstar cutoff eta hcut K W
  | succ n ih =>
      intro W lo hi hlo hhi hsW
      obtain ⟨Vlog,Alog,hbox,hone⟩:=href lo hi hlo hhi
      exact rank_energy_exists_succ_of_reference n L cstar cutoff eta K hL hcstar hcut hcutL
        hcutc heta heta1 hetac hetad ih W lo hi hlo hhi hsW Vlog Alog hbox hone
        (fun window=>hthreshold eta heta hi Alog window)

theorem canonical_energy_exists_of_references_oai
    (href:RankReferenceCutoffs)(hthreshold:RankReferenceThresholds)
    (Mcap Fcap c eps:ℝ)(hM:0≤Mcap)(hF:0≤Fcap)(hc:0<c)(heps:0<eps)
    (K:ℕ)(W:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hhi:0≤hi)
    (hsW:Function.support (W:ℝ→ℂ)⊆Set.Icc lo hi):
    CanonicalEnergyExists Mcap Fcap c eps (Fcap+1) K W :=by
  obtain ⟨n,cutoff,eta,hn,hpos,hcut,heta,heta1,hetad,hcutL,hcutc,hetac,hrow,hcap,hmargin0,hmargin,hloss0,hloss⟩:=
    actual_rank_top_parameters Mcap Fcap c eps hM hF hc heps
  have he:=rank_energy_exists_all_of_references href hthreshold (Fcap+1) c cutoff eta K
    (by linarith) hc hcut hcutL hcutc heta heta1 hetac hetad n W lo hi hlo hhi hsW
  exact canonical_energy_of_rank n (Fcap+1) c cutoff eta Mcap Fcap c eps K W
    hrow hcap hmargin hloss.le he

end SevenEighths.InverseMoment

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.InverseMoment.canonical_energy_exists_of_references_oai := @OAI.SevenEighths.InverseMoment.canonical_energy_exists_of_references_oai

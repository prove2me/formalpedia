-- Prove2me | solution 1 for OAI.ClassicalON.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T02:58:28.104304+00:00
-- url     : https://prove2.me/submissions/bd294c17-3196-41ca-aff6-ed6520624f0c

import Mathlib
import Definitions.Def_ClassicalON
import Definitions.Def_OAIQWCO002
import Theorems.Thm_OAI_ClassicalON_LatticeGraph_connection_exponential

section
-- module Solutions.OAIQW_ClassicalON.FiniteVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uF uR uS uV uΩ

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace ClassicalON

theorem spinRotation_preserves_surface {n : ℕ}
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving (spinRotation R)
      (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
      (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere := by
  open scoped Pointwise in
  refine ⟨(spinRotation R).measurable, Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply (spinRotation R).measurable hs,
    Measure.toSphere_apply' _ ((spinRotation R).measurable hs),
    Measure.toSphere_apply' _ hs]
  congr 1
  have hcone : Set.Ioo (0 : ℝ) 1 • (Subtype.val '' ((spinRotation R) ⁻¹' s)) =
      R ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
    ext v
    constructor
    · rintro ⟨r, hr, w, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨r, hr, R t.val, ⟨spinRotation R t, ht, rfl⟩, (R.map_smul r t.val).symm⟩
    · rintro ⟨r, hr, w, ⟨t, ht, rfl⟩, hv⟩
      refine ⟨r, hr, R.symm t.val, ⟨(spinRotation R).symm t, ?_, rfl⟩, ?_⟩
      · simpa only [Set.mem_preimage, Homeomorph.apply_symm_apply] using ht
      · apply R.injective
        simpa only [map_smul, LinearIsometryEquiv.apply_symm_apply] using hv
  rw [hcone]
  have hm := R.toHomeomorph.measurableEmbedding.map_apply
    (volume : Measure (EuclideanSpace ℝ (Fin n)))
    (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s))
  change (Measure.map R volume) _ = volume (R ⁻¹' _) at hm
  rw [R.measurePreserving.map_eq] at hm
  exact hm.symm

theorem spinRotation_preserves_probability {n : ℕ}
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving (spinRotation R) (sphereProbability n) (sphereProbability n) :=
  (spinRotation_preserves_surface R).smul_measure _

open scoped Matrix

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.AssociationCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uY

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace ClassicalON

section CompactIntegral
variable {X : Type uX} {Y : Type uY} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {μ : Measure X} [IsFiniteMeasure μ]

theorem compact_integrable {f : X → ℝ} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem compact_integral_pos [IsProbabilityMeasure μ] {w : X → ℝ}
    (hw : Continuous w) (hp : ∀ x,0<w x) : 0<∫ x,w x ∂μ := by
  apply (integral_pos_iff_support_of_nonneg (fun x => (hp x).le) (compact_integrable hw)).2
  have he : Function.support w=univ := by ext x; simp [Function.mem_support,(hp x).ne']
  rw [he,measure_univ]
  exact zero_lt_one

omit [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y] in
theorem compact_parametric_integral [FirstCountableTopology Y] [LocallyCompactSpace Y]
    (f : Y → X → ℝ) (hf : Continuous f.uncurry) : Continuous (fun y => ∫ x,f y x ∂μ) := by
  simpa only [Measure.restrict_univ] using
    (continuous_parametric_integral_of_continuous hf (isCompact_univ : IsCompact (univ : Set X)))

end CompactIntegral

section Weighted
variable {X : Type uX} [MeasurableSpace X] [TopologicalSpace X] [CompactSpace X]
  [BorelSpace X] {μ : Measure X} [IsProbabilityMeasure μ] {w : X → ℝ}
  (hw : Continuous w) (hp : ∀ x,0<w x)

include hw hp

theorem weightedMean_nonneg {f : X → ℝ} (hf : ∀ x,0≤f x) : 0≤weightedMean μ w f := by
  exact div_nonneg (integral_nonneg (fun x => mul_nonneg (hp x).le (hf x)))
    (compact_integral_pos hw hp).le

theorem weightedMean_mono {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x,f x≤g x) : weightedMean μ w f ≤ weightedMean μ w g := by
  exact div_le_div_of_nonneg_right
    (integral_mono (compact_integrable (hw.mul hf)) (compact_integrable (hw.mul hg))
      (fun x => mul_le_mul_of_nonneg_left (hfg x) (hp x).le)) (compact_integral_pos hw hp).le

end Weighted

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.FerromagneticMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uX

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace ClassicalON

section
variable {X : Type uX} {E : Type uE} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [Fintype E] (μ : Measure X) [IsProbabilityMeasure μ]
  (T : E → X → ℝ)

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem continuous_edgeHamiltonian (hT : ∀ e,Continuous (T e)) (b : E → ℝ) :
    Continuous (edgeHamiltonian T b) := by
  exact continuous_finsetSum _ (fun e _ => continuous_const.mul (hT e))

end
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.AmplitudePartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV uX

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace ClassicalON

section
variable {X : Type uX} {V : Type uV} {E : Type uE} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [Fintype E] (μ : Measure X) [IsProbabilityMeasure μ]
  (T : E → X → ℝ) (left right : E → V) (b : E → ℝ)

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
 theorem continuous_amplitudeHamiltonian (hT : ∀ e,Continuous (T e)) :
    Continuous (fun p : (V → ℝ)×X => edgeHamiltonian T
      (amplitudeCoupling left right b p.1) p.2) := by
  unfold edgeHamiltonian amplitudeCoupling
  fun_prop

theorem amplitudePartition_pos (hT : ∀ e,Continuous (T e)) (a : V → ℝ) :
    0<amplitudePartition μ T left right b a := by
  exact compact_integral_pos (continuous_edgeHamiltonian T hT _).rexp (fun x => Real.exp_pos _)

theorem continuous_amplitudePartition [Fintype V] (hT : ∀ e,Continuous (T e)) :
    Continuous (amplitudePartition μ T left right b) := by
  exact compact_parametric_integral _ (continuous_amplitudeHamiltonian T left right b hT).rexp

end
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.PlanarAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
namespace ClassicalON

open scoped ComplexConjugate

theorem continuous_planarCos : Continuous planarCos := by
  unfold planarCos planarCharacter
  exact Complex.continuous_re.comp (continuous_subtype_val.comp AddCircle.continuous_toCircle)

theorem continuous_planarSin : Continuous planarSin := by
  unfold planarSin planarCharacter
  exact Complex.continuous_im.comp (continuous_subtype_val.comp AddCircle.continuous_toCircle)

theorem planarCharacter_add (x y : PlanarAngle) :
    planarCharacter (x+y)=planarCharacter x*planarCharacter y := by
  simp only [planarCharacter,AddCircle.toCircle_add,Circle.coe_mul]

theorem planarCharacter_neg (x : PlanarAngle) :
    planarCharacter (-x)=conj (planarCharacter x) := by
  simp only [planarCharacter,AddCircle.toCircle_neg,Circle.coe_inv_eq_conj]

variable {V : Type uV} {E : Type uE}

theorem continuous_planarEnergy (left right : E → V) (e : E) :
    Continuous (planarEnergy left right e) := by
  exact continuous_planarCos.comp ((continuous_apply _).sub (continuous_apply _))

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.AmplitudeLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory Set
namespace ClassicalON

theorem continuous_transverseAmplitude : Continuous transverseAmplitude := by
  unfold transverseAmplitude; fun_prop

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

theorem isingAmplitudePartition_pos (left right : E → V) (b : E → ℝ) (r : V → Amplitude) :
    0 < isingAmplitudePartition left right b r :=
  amplitudePartition_pos _ _ _ _ _ (fun _ => continuous_of_discreteTopology) _

theorem planarAmplitudePartition_pos (left right : E → V) (b : E → ℝ) (r : V → Amplitude) :
    0<planarAmplitudePartition left right b r :=
  amplitudePartition_pos _ _ _ _ _ (continuous_planarEnergy _ _) _

theorem continuous_isingAmplitudePartition (left right : E → V) (b : E → ℝ) :
    Continuous (isingAmplitudePartition left right b) := by
  apply (continuous_amplitudePartition isingReference (isingEnergy left right) left right b
    (fun _ => continuous_of_discreteTopology)).comp
  fun_prop

theorem continuous_planarAmplitudePartition (left right : E → V) (b : E → ℝ) :
    Continuous (planarAmplitudePartition left right b) := by
  apply (continuous_amplitudePartition planarReference (planarEnergy left right) left right b
    (continuous_planarEnergy _ _)).comp
  exact continuous_pi (fun v => continuous_transverseAmplitude.comp (continuous_apply v))

theorem amplitudeDensity_pos (left right : E → V) (b : E → ℝ) (r : V → Amplitude) :
    0<amplitudeDensity left right b r :=
  mul_pos (isingAmplitudePartition_pos _ _ _ _) (planarAmplitudePartition_pos _ _ _ _)

theorem continuous_amplitudeDensity (left right : E → V) (b : E → ℝ) :
    Continuous (amplitudeDensity left right b) :=
  (continuous_isingAmplitudePartition _ _ _).mul (continuous_planarAmplitudePartition _ _ _)

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.CylindricalGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace ClassicalON

theorem planarCos_add (θ φ : PlanarAngle) :
    planarCos (θ+φ)=planarCos θ*planarCos φ-planarSin θ*planarSin φ := by
  simp [planarCos,planarSin,planarCharacter_add,Complex.mul_re]

theorem planarSin_add (θ φ : PlanarAngle) :
    planarSin (θ+φ)=planarSin θ*planarCos φ+planarCos θ*planarSin φ := by
  simp [planarCos,planarSin,planarCharacter_add,Complex.mul_im,add_comm]

theorem continuous_cylindricalSpin :
    Continuous (fun p : Amplitude×Bool×PlanarAngle => cylindricalSpin p.1 p.2.1 p.2.2) := by
  apply Continuous.subtype_mk
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun p : Amplitude×Bool×PlanarAngle => (p.1:ℝ)*signValue p.2.1)
    exact continuous_fst.subtype_val.mul ((show Continuous signValue from continuous_of_discreteTopology).comp (continuous_fst.comp continuous_snd))
  · exact (continuous_transverseAmplitude.comp continuous_fst).mul
      (continuous_planarCos.comp (continuous_snd.comp continuous_snd))
  · exact (continuous_transverseAmplitude.comp continuous_fst).mul
      (continuous_planarSin.comp (continuous_snd.comp continuous_snd))

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.CylindricalFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace ClassicalON

theorem continuous_firstAmplitude : Continuous firstAmplitude := by
  apply Continuous.subtype_mk
  exact ((PiLp.continuous_apply 2 _ 0).comp continuous_subtype_val).abs

theorem planarAngle_exists (a b : ℝ) (hab : a^2+b^2=1) :
    ∃ θ : PlanarAngle,planarCos θ=a ∧ planarSin θ=b := by
  let z : Circle := ⟨⟨a,b⟩,by
    change (⟨a,b⟩ : ℂ) ∈ Metric.sphere 0 1
    rw [mem_sphere_zero_iff_norm]
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1)).mp
    rw [← Complex.normSq_eq_norm_sq]
    simpa [Complex.normSq_apply,pow_two] using hab⟩
  obtain ⟨θ,hθ⟩ := (AddCircle.homeomorphCircle (T := (1:ℝ)) (by norm_num)).surjective z
  rw [AddCircle.homeomorphCircle_apply] at hθ
  exact ⟨θ,congrArg (fun z : Circle => (z:ℂ).re) hθ,congrArg (fun z : Circle => (z:ℂ).im) hθ⟩

theorem cylindricalSpin_surjective_fiber (s : Spin 3) :
    ∃ τ θ,cylindricalSpin (firstAmplitude s) τ θ=s := by
  let r := firstAmplitude s
  let q := transverseAmplitude r
  have hq : q^2=s.val 1^2+s.val 2^2 := by
    have hh := normSq_three s.val
    rw [spin_norm] at hh
    have hr : (r:ℝ)^2=s.val 0^2 := sq_abs _
    dsimp only [q]
    rw [transverseAmplitude_sq,hr]
    nlinarith
  obtain ⟨τ,hτ⟩ : ∃ τ,(r:ℝ)*signValue τ=s.val 0 := by
    by_cases hs : 0 ≤ s.val 0
    · exact ⟨true,by simp [r,firstAmplitude,signValue,abs_of_nonneg hs]⟩
    · exact ⟨false,by simp [r,firstAmplitude,signValue,abs_of_neg (lt_of_not_ge hs)]⟩
  by_cases hzero : q=0
  · refine ⟨τ,0,Subtype.ext ?_⟩
    ext i
    have h1 : s.val 1=0 := by nlinarith [sq_nonneg (s.val 2)]
    have h2 : s.val 2=0 := by nlinarith [sq_nonneg (s.val 1)]
    fin_cases i
    · exact hτ
    · change q*planarCos 0=s.val 1
      rw [hzero,h1,zero_mul]
    · change q*planarSin 0=s.val 2
      rw [hzero,h2,zero_mul]
  · have hab : (s.val 1/q)^2+(s.val 2/q)^2=1 := by
      field_simp
      nlinarith
    obtain ⟨θ,hc,hs⟩ := planarAngle_exists _ _ hab
    refine ⟨τ,θ,Subtype.ext ?_⟩
    ext i
    fin_cases i
    · exact hτ
    · change q*planarCos θ=s.val 1
      rw [hc,mul_div_cancel₀ _ hzero]
    · change q*planarSin θ=s.val 2
      rw [hs,mul_div_cancel₀ _ hzero]

theorem cylinderRotation_cylindricalSpin (τ υ : Bool) (θ φ : PlanarAngle) (r : Amplitude) :
    spinRotation (cylinderRotation τ θ) (cylindricalSpin r υ φ)=
      cylindricalSpin r (τ==υ) (θ+φ) := by
  apply Subtype.ext
  ext i
  fin_cases i
  · change signValue τ*((r:ℝ)*signValue υ)=(r:ℝ)*signValue (τ==υ)
    cases τ <;> cases υ <;> simp [signValue]
  · change planarCos θ*(transverseAmplitude r*planarCos φ)-
      planarSin θ*(transverseAmplitude r*planarSin φ)=transverseAmplitude r*planarCos (θ+φ)
    rw [planarCos_add]; ring
  · change planarSin θ*(transverseAmplitude r*planarCos φ)+
      planarCos θ*(transverseAmplitude r*planarSin φ)=transverseAmplitude r*planarSin (θ+φ)
    rw [planarSin_add]; ring

theorem continuous_cylinderSpinRotation :
    Continuous (fun p : (Bool×PlanarAngle)×Spin 3 =>
      spinRotation (cylinderRotation p.1.1 p.1.2) p.2) := by
  apply Continuous.subtype_mk
  change Continuous (fun p : (Bool×PlanarAngle)×Spin 3 => cylinderLinear p.1.1 p.1.2 p.2.val)
  unfold cylinderLinear
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  have hc : Continuous (fun p : (Bool×PlanarAngle)×Spin 3 => planarCos p.1.2) := continuous_planarCos.comp (continuous_snd.comp continuous_fst)
  have hs : Continuous (fun p : (Bool×PlanarAngle)×Spin 3 => planarSin p.1.2) := continuous_planarSin.comp (continuous_snd.comp continuous_fst)
  have ht : Continuous (fun p : (Bool×PlanarAngle)×Spin 3 => signValue p.1.1) := (show Continuous signValue from continuous_of_discreteTopology).comp (continuous_fst.comp continuous_fst)
  have hv (j : Fin 3) : Continuous (fun p : (Bool×PlanarAngle)×Spin 3 => p.2.val j) := (PiLp.continuous_apply 2 _ j).comp (continuous_subtype_val.comp continuous_snd)
  fin_cases i
  · exact ht.mul (hv 0)
  · exact (hc.mul (hv 1)).sub (hs.mul (hv 2))
  · exact (hs.mul (hv 1)).add (hc.mul (hv 2))

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.CylindricalLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ClassicalON

instance sphericalAmplitudeLaw_isProbability : IsProbabilityMeasure sphericalAmplitudeLaw :=
  (Measure.isProbabilityMeasure_map_iff continuous_firstAmplitude.measurable.aemeasurable).2 inferInstance

theorem integral_signLaw (f : Bool → ℝ) : (∫ τ,f τ ∂signLaw)=(f false+f true)/2 := by
  simp [signLaw,integral_smul_measure,integral_count,div_eq_mul_inv]
  ring

theorem integral_cylinderLaw (f : Bool×PlanarAngle → ℝ) (hf : Continuous f) :
    (∫ p,f p ∂cylinderLaw)=((∫ θ,f (false,θ) ∂angleLaw)+(∫ θ,f (true,θ) ∂angleLaw))/2 := by
  rw [cylinderLaw,integral_prod _ (compact_integrable hf),integral_signLaw]

theorem cylinder_orbit_average (f : Spin 3 → ℝ) (hf : Continuous f) (s : Spin 3) :
    (∫ p,f (spinRotation (cylinderRotation p.1 p.2) s) ∂cylinderLaw)=
      ∫ p,f (cylindricalSpin (firstAmplitude s) p.1 p.2) ∂cylinderLaw := by
  obtain ⟨υ,φ,hspin⟩ := cylindricalSpin_surjective_fiber s
  have he (p : Bool×PlanarAngle) :
      spinRotation (cylinderRotation p.1 p.2) s=
        cylindricalSpin (firstAmplitude s) (p.1==υ) (p.2+φ) := by
    conv_lhs => rw [← hspin]
    rw [cylinderRotation_cylindricalSpin]
  simp_rw [he]
  have hc : Continuous (fun p : Bool×PlanarAngle => f (cylindricalSpin (firstAmplitude s) p.1 p.2)) :=
    hf.comp (continuous_cylindricalSpin.comp (continuous_const.prodMk continuous_id))
  have hm : Continuous (fun p : Bool×PlanarAngle => (p.1==υ,p.2+φ)) :=
    ((show Continuous (fun τ : Bool => τ==υ) from continuous_of_discreteTopology).comp continuous_fst).prodMk
      (continuous_snd.add continuous_const)
  have hh : Continuous (fun p : Bool×PlanarAngle => f (cylindricalSpin (firstAmplitude s) (p.1==υ) (p.2+φ))) := hc.comp hm
  rw [integral_cylinderLaw _ hh,integral_cylinderLaw _ hc]
  have hshift (τ : Bool) :
      (∫ θ,f (cylindricalSpin (firstAmplitude s) τ (θ+φ)) ∂angleLaw)=
        ∫ θ,f (cylindricalSpin (firstAmplitude s) τ θ) ∂angleLaw :=
    integral_add_right_eq_self (fun θ => f (cylindricalSpin (firstAmplitude s) τ θ)) φ
  cases υ <;> simp only [Bool.false_beq,Bool.true_beq,Bool.not_false,Bool.not_true]
  all_goals rw [hshift,hshift]
  all_goals ring

theorem integral_sphere_orbit (f : Spin 3 → ℝ) (hf : Continuous f) :
    (∫ s,∫ p,f (spinRotation (cylinderRotation p.1 p.2) s) ∂cylinderLaw ∂sphereProbability 3)=
      ∫ s,f s ∂sphereProbability 3 := by
  have hcont : Continuous (fun p : Spin 3×(Bool×PlanarAngle) => f (spinRotation (cylinderRotation p.2.1 p.2.2) p.1)) :=
    hf.comp (continuous_cylinderSpinRotation.comp (f := (Prod.swap : Spin 3×(Bool×PlanarAngle) → (Bool×PlanarAngle)×Spin 3)) continuous_swap)
  have hi := integral_integral_swap (μ := sphereProbability 3) (ν := cylinderLaw)
    (f := fun s p => f (spinRotation (cylinderRotation p.1 p.2) s))
    (compact_integrable hcont)
  rw [hi]
  have hp (p : Bool×PlanarAngle) :
      (∫ s,f (spinRotation (cylinderRotation p.1 p.2) s) ∂sphereProbability 3)=∫ s,f s ∂sphereProbability 3 :=
    (spinRotation_preserves_probability _).integral_comp (spinRotation _).measurableEmbedding f
  simp_rw [hp]
  simp

theorem integral_sphere_cylinder (f : Spin 3 → ℝ) (hf : Continuous f) :
    (∫ s,f s ∂sphereProbability 3)=
      ∫ r,∫ p,f (cylindricalSpin r p.1 p.2) ∂cylinderLaw ∂sphericalAmplitudeLaw := by
  have hc : Continuous (fun p : Amplitude×(Bool×PlanarAngle) => f (cylindricalSpin p.1 p.2.1 p.2.2)) :=
    hf.comp continuous_cylindricalSpin
  have hm : Continuous (fun r => ∫ p,f (cylindricalSpin r p.1 p.2) ∂cylinderLaw) :=
    compact_parametric_integral _ hc
  rw [sphericalAmplitudeLaw,integral_map continuous_firstAmplitude.measurable.aemeasurable hm.measurable.aestronglyMeasurable]
  calc
    _ = ∫ s,∫ p,f (spinRotation (cylinderRotation p.1 p.2) s) ∂cylinderLaw ∂sphereProbability 3 :=
      (integral_sphere_orbit f hf).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall (cylinder_orbit_average f hf))

theorem cylindricalSpin_preserves : MeasurePreserving
    (fun p : Amplitude×Bool×PlanarAngle => cylindricalSpin p.1 p.2.1 p.2.2)
    (sphericalAmplitudeLaw.prod cylinderLaw) (sphereProbability 3) := by
  refine ⟨continuous_cylindricalSpin.measurable,?_⟩
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have hc : Continuous (fun p : Amplitude×Bool×PlanarAngle => f (cylindricalSpin p.1 p.2.1 p.2.2)) :=
    f.continuous.comp continuous_cylindricalSpin
  rw [integral_map (f := fun x => f x) continuous_cylindricalSpin.measurable.aemeasurable f.continuous.aestronglyMeasurable,
    integral_prod _ (compact_integrable hc)]
  exact (integral_sphere_cylinder f f.continuous).symm

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.CylindricalConfiguration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

omit [Fintype V] in
theorem continuous_freeSpinEnergy (n : ℕ) (left right : E → V) (b : E → ℝ) :
    Continuous (freeSpinEnergy n left right b) := by unfold freeSpinEnergy; fun_prop

omit [Fintype V] [Fintype E] in
theorem continuous_cylindricalConfiguration :
    Continuous (fun p : (V → Amplitude)×(V → Bool)×(V → PlanarAngle) =>
      cylindricalConfiguration p.1 p.2.1 p.2.2) := by
  apply continuous_pi
  intro v
  exact continuous_cylindricalSpin.comp
    (f := fun p : (V → Amplitude)×(V → Bool)×(V → PlanarAngle) => (p.1 v,p.2.1 v,p.2.2 v))
    (((continuous_apply v).comp continuous_fst).prodMk
      (((continuous_apply v).comp (continuous_fst.comp continuous_snd)).prodMk
        ((continuous_apply v).comp (continuous_snd.comp continuous_snd))))

omit [Fintype E] in
theorem cylindricalConfiguration_preserves : MeasurePreserving
    (fun p : (V → Amplitude)×(V → Bool)×(V → PlanarAngle) => cylindricalConfiguration p.1 p.2.1 p.2.2)
    ((Measure.pi fun _ : V => sphericalAmplitudeLaw).prod ((isingReference (V := V)).prod planarReference))
    (freeSpinReference 3) := by
  let A := MeasurableEquiv.arrowProdEquivProdArrow Amplitude (Bool×PlanarAngle) V
  let B := MeasurableEquiv.arrowProdEquivProdArrow Bool PlanarAngle V
  have hA := (measurePreserving_arrowProdEquivProdArrow Amplitude (Bool×PlanarAngle) V
    (fun _ => sphericalAmplitudeLaw) (fun _ => cylinderLaw)).symm A
  have hB := (measurePreserving_arrowProdEquivProdArrow Bool PlanarAngle V
    (fun _ => signLaw) (fun _ => angleLaw)).symm B
  have h1 := (MeasurePreserving.id (Measure.pi fun _ : V => sphericalAmplitudeLaw)).prod hB
  have h2 := hA.comp h1
  have h3 := measurePreserving_pi (fun _ : V => sphericalAmplitudeLaw.prod cylinderLaw)
    (fun _ => sphereProbability 3) (fun _ => cylindricalSpin_preserves)
  exact h3.comp h2

omit [Fintype E] in
theorem integral_freeSpinReference_cylinder (f : (V → Spin 3) → ℝ) (hf : Continuous f) :
    (∫ s,f s ∂freeSpinReference 3)=
      ∫ r,∫ τ,∫ θ,f (cylindricalConfiguration r τ θ) ∂planarReference ∂isingReference
        ∂Measure.pi (fun _ : V => sphericalAmplitudeLaw) := by
  let : BorelSpace ((V → Amplitude) × (V → Bool) × (V → PlanarAngle)) := Prod.borelSpace
  have hc : Continuous (fun p : (V → Amplitude)×(V → Bool)×(V → PlanarAngle) =>
      f (cylindricalConfiguration p.1 p.2.1 p.2.2)) := hf.comp continuous_cylindricalConfiguration
  rw [← cylindricalConfiguration_preserves.map_eq,
    integral_map continuous_cylindricalConfiguration.measurable.aemeasurable hf.aestronglyMeasurable,
    integral_prod _ (compact_integrable hc)]
  apply integral_congr_ae
  filter_upwards with r
  have hr : Continuous (fun p : (V → Bool)×(V → PlanarAngle) => f (cylindricalConfiguration r p.1 p.2)) :=
    hc.comp (continuous_const.prodMk continuous_id)
  exact integral_prod _ (compact_integrable hr)

omit [Fintype V] [Fintype E] in
theorem cylindricalSpin_inner (r q : Amplitude) (τ υ : Bool) (θ φ : PlanarAngle) :
    ⟪(cylindricalSpin r τ θ).val,(cylindricalSpin q υ φ).val⟫_ℝ=
      (r:ℝ)*(q:ℝ)*(signValue τ*signValue υ)+
        transverseAmplitude r*transverseAmplitude q*planarCos (θ-φ) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct,Fin.sum_univ_succ,Fin.isValue,cylindricalSpin,
    WithLp.ofLp_toLp,Matrix.cons_val_zero,Matrix.cons_val_succ,star_trivial,Finset.univ_eq_empty,
    Finset.sum_empty,add_zero]
  simp only [planarCos,planarSin,sub_eq_add_neg,planarCharacter_add,planarCharacter_neg,
    Complex.mul_re,Complex.conj_re,Complex.conj_im]
  ring

omit [Fintype V] in
theorem cylindricalConfiguration_energy (left right : E → V) (b : E → ℝ)
    (r : V → Amplitude) (τ : V → Bool) (θ : V → PlanarAngle) :
    freeSpinEnergy 3 left right b (cylindricalConfiguration r τ θ)=
      edgeHamiltonian (isingEnergy left right) (amplitudeCoupling left right b (fun v => (r v:ℝ))) τ+
      edgeHamiltonian (planarEnergy left right) (amplitudeCoupling left right b (fun v => transverseAmplitude (r v))) θ := by
  unfold freeSpinEnergy edgeHamiltonian cylindricalConfiguration
  simp_rw [cylindricalSpin_inner]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  unfold amplitudeCoupling isingEnergy planarEnergy
  ring

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.UpperEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI

noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology Classical
namespace ClassicalON

instance sphericalAmplitudeLaw_isOpenPos : sphericalAmplitudeLaw.IsOpenPosMeasure :=
  continuous_firstAmplitude.isOpenPosMeasure_map (fun r =>
    ⟨cylindricalSpin r true 0,firstAmplitude_cylindricalSpin r true 0⟩)

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.BondSubspace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open scoped BigOperators
namespace ClassicalON

variable {V : Type uV} {E : Type uE}

variable [Fintype V]

omit [Fintype V] in
theorem clusterWeight_pos (left right : E → V) (η : E → Bool) : 0<clusterWeight left right η := by
  unfold clusterWeight; positivity

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.BondLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV uX

noncomputable section
open scoped BigOperators Classical
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

theorem bondProduct_nonneg {t : E → ℝ} (ht : ∀ e,0 ≤ t e) (η : E → Bool) :
    0 ≤ bondProduct t η := Finset.prod_nonneg fun e _ => by split <;> [exact ht e; exact zero_le_one]

omit [Fintype V] in
theorem bondWeight_nonneg (left right : E → V) {t : E → ℝ} (ht : ∀ e,0 ≤ t e)
    (η : E → Bool) : 0 ≤ bondWeight left right t η :=
  mul_nonneg (clusterWeight_pos _ _ _).le (bondProduct_nonneg ht η)

omit [Fintype V] in
theorem bondWeight_sum_pos (left right : E → V) {t : E → ℝ} (ht : ∀ e,0 ≤ t e) :
    0 < ∑ η,bondWeight left right t η := by
  apply Finset.sum_pos' (fun η _ => bondWeight_nonneg left right ht η)
  refine ⟨fun _ => false,Finset.mem_univ _,?_⟩
  simpa [bondWeight,bondProduct] using clusterWeight_pos left right (fun _ => false)

section Finite
variable {X : Type uX} [Fintype X]

theorem finiteMean_nonneg {w f : X → ℝ} (hw : ∀ x,0 ≤ w x) (hf : ∀ x,0 ≤ f x) :
    0 ≤ finiteMean w f :=
  div_nonneg (Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (hf x)) (Finset.sum_nonneg fun x _ => hw x)

theorem finiteMean_mono {w f g : X → ℝ} (hw : ∀ x,0 ≤ w x) (hf : f ≤ g) :
    finiteMean w f ≤ finiteMean w g := by
  apply div_le_div_of_nonneg_right _ (Finset.sum_nonneg fun x _ => hw x)
  exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hf x) (hw x)

end Finite

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.BondSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open scoped BigOperators Classical
namespace ClassicalON

theorem signField_cases (a : SignField) : a=0 ∨ a=1 := by
  fin_cases a <;> [exact Or.inl rfl; exact Or.inr rfl]

theorem fieldSign_add (a b : SignField) : fieldSign (a+b)=fieldSign a*fieldSign b := by
  have htwo : (1 : SignField)+1=0 := rfl
  rcases signField_cases a with rfl | rfl <;> rcases signField_cases b with rfl | rfl <;> simp [htwo]

theorem fieldSign_sq (a : SignField) : fieldSign a*fieldSign a=1 := by
  rcases signField_cases a with rfl | rfl <;> simp

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

omit [Fintype E] in
theorem compatibleSigns_card (left right : E → V) (η : E → Bool) :
    Fintype.card (compatibleSigns left right η)=2^bondRank left right η := by
  rw [Fintype.card_congr (compatibleSignsEquiv left right η),Module.card_eq_pow_finrank (K := SignField)]
  simp [bondRank,SignField]

omit [Fintype E] in
theorem compatibleSigns_sum (left right : E → V) (η : E → Bool) :
    (∑ s : V → Bool,if s∈compatibleSigns left right η then (1:ℝ) else 0)=clusterWeight left right η := by
  rw [Finset.sum_boole,← Fintype.card_subtype]
  unfold clusterWeight
  exact_mod_cast compatibleSigns_card left right η

omit [Fintype E] in
theorem bond_sign_correlation (left right : E → V) (η : E → Bool) (x y : V) :
    (∑ s : bondSubspace left right η,fieldSign (s.val x)*fieldSign (s.val y))=
      if bondConnected left right η x y then clusterWeight left right η else 0 := by
  split_ifs with h
  · have he (s : bondSubspace left right η) : fieldSign (s.val x)*fieldSign (s.val y)=1 := by
      rw [h s.val s.property]; exact fieldSign_sq _
    simp_rw [he]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    unfold clusterWeight bondRank
    norm_cast
    rw [Module.card_eq_pow_finrank (K := SignField)]
    simp [SignField]
  · obtain ⟨s,hs,hxy⟩ : ∃ s∈bondSubspace left right η,s x≠s y := by
      unfold bondConnected at h
      push Not at h
      exact h
    let u : bondSubspace left right η := ⟨s,hs⟩
    have hc : fieldSign (s x)*fieldSign (s y)= -1 := by
      have hlocal (a b : SignField) (hab : a≠b) : fieldSign a*fieldSign b= -1 := by
        rcases signField_cases a with rfl | rfl <;> rcases signField_cases b with rfl | rfl <;> simp_all
      exact hlocal _ _ hxy
    have hh := Equiv.sum_comp (Equiv.addRight u) (fun t : bondSubspace left right η => fieldSign (t.val x)*fieldSign (t.val y))
    have he (t : bondSubspace left right η) :
        fieldSign ((t+u).val x)*fieldSign ((t+u).val y)= -(fieldSign (t.val x)*fieldSign (t.val y)) := by
      change fieldSign (t.val x+s x)*fieldSign (t.val y+s y)= _
      rw [fieldSign_add,fieldSign_add,mul_mul_mul_comm,hc,mul_neg_one]
    change (∑ t : bondSubspace left right η,fieldSign ((t+u).val x)*fieldSign ((t+u).val y))=_ at hh
    simp_rw [he] at hh
    rw [Finset.sum_neg_distrib] at hh
    linarith

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.DiscreteReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace ClassicalON

variable {V : Type uV} [Fintype V]

theorem isingReference_singleton (s : V → Bool) :
    isingReference {s}=(2 : ℝ≥0∞)⁻¹^Fintype.card V := by
  classical
  rw [isingReference,Measure.pi_singleton]
  simp [signLaw]

open scoped Classical in
theorem integral_isingReference (f : (V → Bool) → ℝ) :
    (∫ s,f s ∂isingReference)=(2 : ℝ)⁻¹^Fintype.card V*∑ s,f s := by
  classical
  rw [integral_fintype (compact_integrable continuous_of_discreteTopology)]
  simp only [Measure.real,isingReference_singleton,ENNReal.toReal_pow,ENNReal.toReal_inv,
    ENNReal.toReal_ofNat,smul_eq_mul,← Finset.mul_sum]

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.BondExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

omit [Fintype V] in
theorem bondSignProduct_eq (left right : E → V) (t : E → ℝ) (η : E → Bool) (s : V → Bool) :
    bondSignProduct left right t η s=
      bondProduct t η*(if s∈compatibleSigns left right η then 1 else 0) := by
  by_cases h : s∈compatibleSigns left right η
  · simp only [h,ite_true,mul_one,bondSignProduct,bondProduct]
    apply Finset.prod_congr rfl
    intro e _
    cases he : η e
    · simp
    · simp [h e he]
  · simp only [h,ite_false,mul_zero]
    obtain ⟨e,he,hs⟩ : ∃ e,η e=true ∧ s (left e)≠s (right e) := by
      change ¬(∀ e,η e=true → s (left e)=s (right e)) at h
      push Not at h
      exact h
    apply Finset.prod_eq_zero (Finset.mem_univ e)
    simp [he,hs]

omit [Fintype V] in
theorem ising_expansion (left right : E → V) (K : E → ℝ) (s : V → Bool) :
    Real.exp (edgeHamiltonian (isingEnergy left right) K s)=
      Real.exp (-∑ e,K e)*∑ η : E → Bool,bondSignProduct left right
        (fun e => Real.exp (2*K e)-1) η s := by
  have hedge (k : ℝ) (a b : Bool) :
      Real.exp (k*(signValue a*signValue b))=
        Real.exp (-k)*(∑ η : Bool,if η then (if a=b then Real.exp (2*k)-1 else 0) else 1) := by
    cases a <;> cases b <;> simp [signValue]
    all_goals ring_nf
    all_goals rw [← Real.exp_add]
    all_goals (congr 1; ring)
  unfold edgeHamiltonian isingEnergy
  rw [Real.exp_sum]
  simp_rw [hedge]
  rw [Finset.prod_mul_distrib,← Real.exp_sum,Finset.sum_neg_distrib,Fintype.prod_sum]
  rfl

omit [Fintype V] in
theorem signValue_fieldSign (s : Bool) : signValue s=fieldSign (signFieldEquiv s) := by
  cases s <;> rfl

omit [Fintype E] in
theorem compatible_sign_correlation_sum (left right : E → V) (η : E → Bool) (x y : V) :
    (∑ s : V → Bool,(if s∈compatibleSigns left right η then (1:ℝ) else 0)*
      (signValue (s x)*signValue (s y)))=
      if bondConnected left right η x y then clusterWeight left right η else 0 := by
  have he := Equiv.sum_comp (compatibleSignsEquiv left right η)
    (fun s : bondSubspace left right η => fieldSign (s.val x)*fieldSign (s.val y))
  have hh : (∑ s : compatibleSigns left right η,signValue (s.val x)*signValue (s.val y))=
      ∑ s : bondSubspace left right η,fieldSign (s.val x)*fieldSign (s.val y) := by
    convert he using 1
    congr 1
    ext s
    simp only [signValue_fieldSign]
    rfl
  rw [← bond_sign_correlation left right η x y,← hh]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun s : V → Bool => s∈compatibleSigns left right η))
    (by simp) (fun s => signValue (s x)*signValue (s y)),Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs <;> simp

theorem ising_partition_bond_sum (left right : E → V) (K : E → ℝ) :
    (∫ s,Real.exp (edgeHamiltonian (isingEnergy left right) K s) ∂isingReference)=
      (2 : ℝ)⁻¹^Fintype.card V*Real.exp (-∑ e,K e)*
        ∑ η,bondWeight left right (fun e => Real.exp (2*K e)-1) η := by
  rw [integral_isingReference]
  simp_rw [ising_expansion,bondSignProduct_eq]
  rw [← Finset.mul_sum,Finset.sum_comm]
  simp_rw [← Finset.mul_sum,compatibleSigns_sum]
  unfold bondWeight
  simp only [mul_comm (bondProduct _ _) (clusterWeight _ _ _)]
  ring

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.SpinBondKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in
theorem continuous_spinBondParameter (left right : E → V) (b : E → ℝ) (e : E) :
    Continuous (fun s => spinBondParameter left right b s e) := by
  unfold spinBondParameter
  fun_prop

omit [Fintype V] in
theorem continuous_spinBondWeight (left right : E → V) (b : E → ℝ) (η : E → Bool) :
    Continuous (fun s => spinBondWeight left right b s η) := by
  unfold spinBondWeight
  apply continuous_finsetProd
  intro e _
  split <;> [exact continuous_spinBondParameter _ _ _ _;exact continuous_const.sub (continuous_spinBondParameter _ _ _ _)]

omit [Fintype V] in
theorem spinBondWeight_sum (left right : E → V) (b : E → ℝ) (s : V → Spin 3) :
    (∑ η,spinBondWeight left right b s η)=1 := by
  unfold spinBondWeight
  change (∑ η : E → Bool, ∏ e, (fun (e : E) (z : Bool) => if z then spinBondParameter left right b s e else 1-spinBondParameter left right b s e) e (η e)) = 1
  rw [← Fintype.prod_sum (fun (e : E) (z : Bool) => if z then spinBondParameter left right b s e else 1-spinBondParameter left right b s e)]
  simp

omit [Fintype V] [Fintype E] in
theorem spinBondParameter_cylinder (left right : E → V) (b : E → ℝ)
    (r : V → Amplitude) (τ : V → Bool) (θ : V → PlanarAngle) (e : E) :
    spinBondParameter left right b (cylindricalConfiguration r τ θ) e=
      if τ (left e)=τ (right e) then 1-Real.exp (-2*amplitudeCoupling left right b (fun v => (r v:ℝ)) e) else 0 := by
  have hp : 0≤(r (left e):ℝ)*(r (right e):ℝ) := mul_nonneg (r (left e)).property.1 (r (right e)).property.1
  unfold spinBondParameter cylindricalConfiguration cylindricalSpin
  simp only [Fin.isValue,Matrix.cons_val_zero]
  have hmul : (r (left e):ℝ)*signValue (τ (left e))*((r (right e):ℝ)*signValue (τ (right e)))=
      (r (left e):ℝ)*(r (right e):ℝ)*(signValue (τ (left e))*signValue (τ (right e))) := by ring
  rw [hmul]
  cases τ (left e) <;> cases τ (right e) <;> simp only [signValue,Bool.false_eq_true,ite_false,ite_true,
    mul_neg,neg_mul,mul_one,neg_neg]
  all_goals simp only [max_eq_left hp,max_eq_right (neg_nonpos.mpr hp),mul_zero,neg_zero,Real.exp_zero,sub_self]
  all_goals (congr 2 <;> (unfold amplitudeCoupling; ring))

omit [Fintype V] in
theorem cylindrical_ising_bond_weight (left right : E → V) (K : E → ℝ) (τ : V → Bool) (η : E → Bool) :
    Real.exp (edgeHamiltonian (isingEnergy left right) K τ)*
      (∏ e,if η e then (if τ (left e)=τ (right e) then 1-Real.exp (-2*K e) else 0)
        else 1-(if τ (left e)=τ (right e) then 1-Real.exp (-2*K e) else 0))=
      Real.exp (-∑ e,K e)*bondSignProduct left right (fun e => Real.exp (2*K e)-1) η τ := by
  have he (k : ℝ) (a d z : Bool) :
      Real.exp (k*(signValue a*signValue d))*(if z then (if a=d then 1-Real.exp (-2*k) else 0)
        else 1-(if a=d then 1-Real.exp (-2*k) else 0))=
      Real.exp (-k)*(if z then (if a=d then Real.exp (2*k)-1 else 0) else 1) := by
    have h1 : Real.exp k*Real.exp (-(2*k))=Real.exp (-k) := by rw [← Real.exp_add]; congr 1; ring
    have h2 : Real.exp (-k)*Real.exp (2*k)=Real.exp k := by rw [← Real.exp_add]; congr 1; ring
    cases a <;> cases d <;> cases z <;> simp [signValue,mul_sub,h1,h2]
  unfold edgeHamiltonian isingEnergy
  rw [Real.exp_sum,← Finset.prod_mul_distrib]
  simp_rw [he]
  rw [Finset.prod_mul_distrib,← Real.exp_sum,Finset.sum_neg_distrib]
  rfl

omit [Fintype V] in
theorem cylindrical_spin_bond_weight (left right : E → V) (b : E → ℝ)
    (r : V → Amplitude) (τ : V → Bool) (θ : V → PlanarAngle) (η : E → Bool) :
    Real.exp (freeSpinEnergy 3 left right b (cylindricalConfiguration r τ θ))*
      spinBondWeight left right b (cylindricalConfiguration r τ θ) η=
      Real.exp (-∑ e,amplitudeCoupling left right b (fun v => (r v:ℝ)) e)*
        bondSignProduct left right (fun e => Real.exp (2*amplitudeCoupling left right b (fun v => (r v:ℝ)) e)-1) η τ*
        Real.exp (edgeHamiltonian (planarEnergy left right)
          (amplitudeCoupling left right b (fun v => transverseAmplitude (r v))) θ) := by
  rw [cylindricalConfiguration_energy,Real.exp_add]
  unfold spinBondWeight
  simp_rw [spinBondParameter_cylinder]
  rw [mul_right_comm, cylindrical_ising_bond_weight]

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.JointBond
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in
theorem amplitudeBondParam_nonneg (left right : E → V) (b : E → ℝ)
    (hb : ∀ e,0 ≤ b e) (r : V → Amplitude) (e : E) :
    0 ≤ amplitudeBondParam left right b r e := by
  apply sub_nonneg.mpr
  apply Real.one_le_exp
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hb e)) (r (left e)).property.1) (r (right e)).property.1

omit [Fintype V] [Fintype E] in
theorem continuous_amplitudeBondParam (left right : E → V) (b : E → ℝ) (e : E) :
    Continuous (fun r => amplitudeBondParam left right b r e) := by
  unfold amplitudeBondParam; fun_prop

omit [Fintype V] in
theorem continuous_bondConditionalMean (left right : E → V) (b : E → ℝ) (hb : ∀ e,0 ≤ b e)
    {f : (V → Amplitude) → (E → Bool) → ℝ} (hf : ∀ η,Continuous (fun r => f r η)) :
    Continuous (bondConditionalMean left right b f) := by
  have hw (η : E → Bool) : Continuous (fun r => bondWeight left right (amplitudeBondParam left right b r) η) := by
    unfold bondWeight bondProduct
    apply Continuous.mul continuous_const
    apply continuous_finsetProd
    intro e _
    split
    · exact continuous_amplitudeBondParam left right b e
    · exact continuous_const
  exact (continuous_finsetSum _ (fun η _ => (hw η).mul (hf η))).div
    (continuous_finsetSum _ (fun η _ => hw η))
    (fun r => (bondWeight_sum_pos left right (amplitudeBondParam_nonneg left right b hb r)).ne')

omit [Fintype V] in
theorem bondConditionalMean_nonneg (left right : E → V) (b : E → ℝ) (hb : ∀ e,0 ≤ b e)
    {f : (V → Amplitude) → (E → Bool) → ℝ} (hf : ∀ r η,0 ≤ f r η) (r : V → Amplitude) :
    0 ≤ bondConditionalMean left right b f r :=
  finiteMean_nonneg (bondWeight_nonneg left right (amplitudeBondParam_nonneg left right b hb r)) (hf r)

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.BondMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

theorem ising_numerator_bond_sum (left right : E → V) (K : E → ℝ) (x y : V) :
    (∫ s,Real.exp (edgeHamiltonian (isingEnergy left right) K s)*(signValue (s x)*signValue (s y)) ∂isingReference)=
      (2:ℝ)⁻¹^Fintype.card V*Real.exp (-∑ e,K e)*
        ∑ η,bondWeight left right (fun e => Real.exp (2*K e)-1) η*
          (if bondConnected left right η x y then 1 else 0) := by
  have hs (η : E → Bool) :
      (∑ s : V → Bool,Real.exp (-∑ e,K e)*(bondProduct (fun e => Real.exp (2*K e)-1) η*
        (if s∈compatibleSigns left right η then 1 else 0))*(signValue (s x)*signValue (s y)))=
        Real.exp (-∑ e,K e)*bondWeight left right (fun e => Real.exp (2*K e)-1) η*
          (if bondConnected left right η x y then 1 else 0) := by
    calc
      _ = (Real.exp (-∑ e,K e)*bondProduct (fun e => Real.exp (2*K e)-1) η)*
          ∑ s : V → Bool,(if s∈compatibleSigns left right η then 1 else 0)*(signValue (s x)*signValue (s y)) := by
        rw [Finset.mul_sum]; congr 1; ext s; ring
      _ = _ := by
        rw [compatible_sign_correlation_sum]
        split_ifs <;> simp [bondWeight]
        ring
  have hall : (∑ s : V → Bool,Real.exp (edgeHamiltonian (isingEnergy left right) K s)*
      (signValue (s x)*signValue (s y)))=
      Real.exp (-∑ e,K e)*∑ η,bondWeight left right (fun e => Real.exp (2*K e)-1) η*
        (if bondConnected left right η x y then 1 else 0) := by
    simp_rw [ising_expansion,bondSignProduct_eq,Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [hs]
    simp_rw [mul_assoc]
  rw [integral_isingReference,hall]
  ring

theorem isingAmplitudePartition_bond_sum (left right : E → V) (b : E → ℝ) (r : V → Amplitude) :
    isingAmplitudePartition left right b r=
      (2:ℝ)⁻¹^Fintype.card V*Real.exp (-∑ e,amplitudeCoupling left right b (fun v => (r v:ℝ)) e)*
        ∑ η,bondWeight left right (amplitudeBondParam left right b r) η := by
  have hp : (fun e => Real.exp (2*amplitudeCoupling left right b (fun v => (r v:ℝ)) e)-1)=
      amplitudeBondParam left right b r := by
    funext e
    unfold amplitudeBondParam amplitudeCoupling
    congr 2
    ring
  rw [isingAmplitudePartition,amplitudePartition,ising_partition_bond_sum,hp]

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.RawBond
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

theorem continuous_amplitudeBondPrefactor (left right : E → V) (b : E → ℝ) :
    Continuous (amplitudeBondPrefactor left right b) := by
  unfold amplitudeBondPrefactor
  apply Continuous.mul _ (continuous_planarAmplitudePartition _ _ _)
  unfold amplitudeCoupling
  fun_prop

theorem continuous_amplitudeBondWeight (left right : E → V) (b : E → ℝ) (η : E → Bool) :
    Continuous (fun r => amplitudeBondWeight left right b r η) := by
  apply (continuous_amplitudeBondPrefactor _ _ _).mul
  unfold bondWeight bondProduct
  apply Continuous.mul continuous_const
  apply continuous_finsetProd
  intro e _
  split
  · exact continuous_amplitudeBondParam left right b e
  · exact continuous_const

theorem amplitudeBondWeight_sum (left right : E → V) (b : E → ℝ) (r : V → Amplitude) :
    (∑ η,amplitudeBondWeight left right b r η)=amplitudeDensity left right b r := by
  unfold amplitudeBondWeight amplitudeDensity
  rw [isingAmplitudePartition_bond_sum]
  rw [← Finset.mul_sum]
  unfold amplitudeBondPrefactor
  ring

theorem amplitudeDensity_bondConditionalMean (left right : E → V) (b : E → ℝ)
    (hb : ∀ e,0≤b e) (f : (V → Amplitude) → (E → Bool) → ℝ) (r : V → Amplitude) :
    amplitudeDensity left right b r*bondConditionalMean left right b f r=
      ∑ η,amplitudeBondWeight left right b r η*f r η := by
  rw [← amplitudeBondWeight_sum left right b r]
  unfold amplitudeBondWeight bondConditionalMean finiteMean
  rw [← Finset.mul_sum]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  have hs := (bondWeight_sum_pos left right (amplitudeBondParam_nonneg left right b hb r)).ne'
  field_simp

theorem jointBondMean_raw (μ : Measure Amplitude) (left right : E → V) (b : E → ℝ)
    (hb : ∀ e,0≤b e) (f : (V → Amplitude) → (E → Bool) → ℝ) :
    jointBondMean μ left right b f=
      (∫ r,∑ η,amplitudeBondWeight left right b r η*f r η ∂Measure.pi (fun _ : V => μ))/
        (∫ r,∑ η,amplitudeBondWeight left right b r η ∂Measure.pi (fun _ : V => μ)) := by
  unfold jointBondMean weightedMean
  simp_rw [amplitudeDensity_bondConditionalMean _ _ _ hb,amplitudeBondWeight_sum]

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.SpinBonds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in
theorem amplitudeBondParam_eq (left right : E → V) (b : E → ℝ) (r : V → Amplitude) :
    (fun e => Real.exp (2*amplitudeCoupling left right b (fun v => (r v:ℝ)) e)-1)=
      amplitudeBondParam left right b r := by
  funext e
  unfold amplitudeBondParam amplitudeCoupling
  congr 2
  ring

theorem integral_spinBondWeight (left right : E → V) (b : E → ℝ) (η : E → Bool) :
    (∫ s,Real.exp (freeSpinEnergy 3 left right b s)*spinBondWeight left right b s η ∂freeSpinReference 3)=
      ∫ r,amplitudeBondWeight left right b r η ∂Measure.pi (fun _ : V => sphericalAmplitudeLaw) := by
  have hc : Continuous (fun s : V → Spin 3 => Real.exp (freeSpinEnergy 3 left right b s)*
      spinBondWeight left right b s η) :=
    (continuous_freeSpinEnergy 3 left right b).rexp.mul (continuous_spinBondWeight left right b η)
  rw [integral_freeSpinReference_cylinder _ hc]
  apply integral_congr_ae
  filter_upwards with r
  simp_rw [cylindrical_spin_bond_weight,integral_const_mul]
  change (∫ τ,Real.exp (-∑ e,amplitudeCoupling left right b (fun v => (r v:ℝ)) e)*
    bondSignProduct left right (fun e => Real.exp (2*amplitudeCoupling left right b (fun v => (r v:ℝ)) e)-1) η τ*
    planarAmplitudePartition left right b r ∂isingReference)=_
  rw [integral_mul_const,integral_const_mul,integral_isingReference]
  simp_rw [bondSignProduct_eq,← Finset.mul_sum,compatibleSigns_sum]
  rw [amplitudeBondParam_eq]
  unfold amplitudeBondWeight amplitudeBondPrefactor bondWeight
  ring

theorem integral_freeSpinWeight (left right : E → V) (b : E → ℝ) :
    (∫ s,Real.exp (freeSpinEnergy 3 left right b s) ∂freeSpinReference 3)=
      ∫ r,amplitudeDensity left right b r ∂Measure.pi (fun _ : V => sphericalAmplitudeLaw) := by
  have he (s : V → Spin 3) : Real.exp (freeSpinEnergy 3 left right b s)=
      ∑ η,Real.exp (freeSpinEnergy 3 left right b s)*spinBondWeight left right b s η := by
    rw [← Finset.mul_sum,spinBondWeight_sum,mul_one]
  rw [show (fun s : V → Spin 3 => Real.exp (freeSpinEnergy 3 left right b s))=
    (fun s => ∑ η,Real.exp (freeSpinEnergy 3 left right b s)*spinBondWeight left right b s η) from funext he]
  rw [integral_finsetSum]
  · simp_rw [integral_spinBondWeight]
    rw [← integral_finsetSum]
    · simp_rw [amplitudeBondWeight_sum]
    · intro η _
      exact compact_integrable (continuous_amplitudeBondWeight _ _ _ _)
  · intro η _
    exact compact_integrable ((continuous_freeSpinEnergy _ _ _ _).rexp.mul (continuous_spinBondWeight _ _ _ _))

theorem freeBondMean_eq_jointBondMean (left right : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e)
    (f : (E → Bool) → ℝ) :
    freeBondMean left right b f=jointBondMean sphericalAmplitudeLaw left right b (fun _ η => f η) := by
  rw [jointBondMean_raw _ _ _ _ hb]
  unfold freeBondMean freeSpinMean weightedMean
  rw [integral_freeSpinWeight]
  simp_rw [amplitudeBondWeight_sum]
  congr 1
  simp_rw [Finset.mul_sum,← mul_assoc]
  rw [integral_finsetSum,integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro η _
    rw [integral_mul_const,integral_mul_const,integral_spinBondWeight]
  · intro η _
    exact (compact_integrable (continuous_amplitudeBondWeight _ _ _ _)).mul_const _
  · intro η _
    exact (compact_integrable ((continuous_freeSpinEnergy _ _ _ _).rexp.mul
      (continuous_spinBondWeight _ _ _ _))).mul_const _

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.SpinCorrelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in
theorem continuous_firstSpinProduct (x y : V) : Continuous (firstSpinProduct x y) := by
  unfold firstSpinProduct
  fun_prop

omit [Fintype V] [Fintype E] in
theorem cylindrical_firstSpinProduct (x y : V) (r : V → Amplitude) (τ : V → Bool) (θ : V → PlanarAngle) :
    firstSpinProduct x y (cylindricalConfiguration r τ θ)=
      (r x:ℝ)*(r y:ℝ)*(signValue (τ x)*signValue (τ y)) := by
  change ((r x:ℝ)*signValue (τ x))*((r y:ℝ)*signValue (τ y))=_
  ring

theorem integral_cylinder_firstSpin (left right : E → V) (b : E → ℝ) (x y : V) (r : V → Amplitude) :
    (∫ τ,∫ θ,Real.exp (freeSpinEnergy 3 left right b (cylindricalConfiguration r τ θ))*
      firstSpinProduct x y (cylindricalConfiguration r τ θ) ∂planarReference ∂isingReference)=
      ∑ η,amplitudeBondWeight left right b r η*
        ((r x:ℝ)*(r y:ℝ)*(if bondConnected left right η x y then 1 else 0)) := by
  have he (τ : V → Bool) (θ : V → PlanarAngle) :
      Real.exp (freeSpinEnergy 3 left right b (cylindricalConfiguration r τ θ))*
        firstSpinProduct x y (cylindricalConfiguration r τ θ)=
      ((r x:ℝ)*(r y:ℝ))*(Real.exp (edgeHamiltonian (isingEnergy left right)
        (amplitudeCoupling left right b (fun v => (r v:ℝ))) τ)*(signValue (τ x)*signValue (τ y)))*
      Real.exp (edgeHamiltonian (planarEnergy left right)
        (amplitudeCoupling left right b (fun v => transverseAmplitude (r v))) θ) := by
    rw [cylindricalConfiguration_energy,Real.exp_add,cylindrical_firstSpinProduct]
    ring
  simp_rw [he,integral_const_mul]
  rw [integral_mul_const,integral_const_mul,ising_numerator_bond_sum,amplitudeBondParam_eq]
  change ((r x:ℝ)*(r y:ℝ))*((2:ℝ)⁻¹^Fintype.card V*
    Real.exp (-∑ e,amplitudeCoupling left right b (fun v => (r v:ℝ)) e)*
      ∑ η,bondWeight left right (amplitudeBondParam left right b r) η*
        (if bondConnected left right η x y then 1 else 0))*planarAmplitudePartition left right b r=_
  rw [Finset.mul_sum,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro η _
  unfold amplitudeBondWeight amplitudeBondPrefactor
  ring

theorem firstSpinMean_eq_jointBondMean (left right : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e) (x y : V) :
    freeSpinMean 3 left right b (firstSpinProduct x y)=
      jointBondMean sphericalAmplitudeLaw left right b
        (fun r η => (r x:ℝ)*(r y:ℝ)*(if bondConnected left right η x y then 1 else 0)) := by
  rw [jointBondMean_raw _ _ _ _ hb]
  unfold freeSpinMean weightedMean
  rw [integral_freeSpinWeight]
  simp_rw [amplitudeBondWeight_sum]
  congr 1
  have hc : Continuous (fun s : V → Spin 3 => Real.exp (freeSpinEnergy 3 left right b s)*firstSpinProduct x y s) :=
    (continuous_freeSpinEnergy 3 left right b).rexp.mul (continuous_firstSpinProduct x y)
  rw [integral_freeSpinReference_cylinder _ hc]
  simp_rw [integral_cylinder_firstSpin]

theorem jointBondMean_nonneg (μ : Measure Amplitude) [IsProbabilityMeasure μ]
    (left right : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e)
    {f : (V → Amplitude) → (E → Bool) → ℝ} (hf : ∀ r η,0≤f r η) :
    0≤jointBondMean μ left right b f :=
  weightedMean_nonneg (continuous_amplitudeDensity _ _ _) (amplitudeDensity_pos _ _ _)
    (bondConditionalMean_nonneg _ _ _ hb hf)

theorem jointBondMean_mono (μ : Measure Amplitude) [IsProbabilityMeasure μ]
    (left right : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e)
    {f g : (V → Amplitude) → (E → Bool) → ℝ}
    (hf : ∀ η,Continuous (fun r => f r η)) (hg : ∀ η,Continuous (fun r => g r η))
    (hfg : ∀ r η,f r η≤g r η) : jointBondMean μ left right b f≤jointBondMean μ left right b g := by
  apply weightedMean_mono (continuous_amplitudeDensity _ _ _) (amplitudeDensity_pos _ _ _)
    (continuous_bondConditionalMean _ _ _ hb hf) (continuous_bondConditionalMean _ _ _ hb hg)
  intro r
  exact finiteMean_mono (bondWeight_nonneg _ _ (amplitudeBondParam_nonneg _ _ _ hb r)) (hfg r)

theorem firstSpinMean_bounds (left right : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e) (x y : V) :
    0≤freeSpinMean 3 left right b (firstSpinProduct x y) ∧
      freeSpinMean 3 left right b (firstSpinProduct x y)≤
        freeBondMean left right b (fun η => if bondConnected left right η x y then 1 else 0) := by
  rw [firstSpinMean_eq_jointBondMean _ _ _ hb,freeBondMean_eq_jointBondMean _ _ _ hb]
  constructor
  · apply jointBondMean_nonneg _ _ _ _ hb
    intro r η
    exact mul_nonneg (mul_nonneg (r x).property.1 (r y).property.1) (by split_ifs <;> norm_num)
  · apply jointBondMean_mono _ _ _ _ hb
    · intro η; fun_prop
    · intro η; exact continuous_const
    · intro r η
      split_ifs <;> simp only [mul_one,mul_zero,le_refl]
      exact (mul_le_of_le_one_left (r y).property.1 (r x).property.2).trans (r y).property.2

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.SpinIsotropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in
theorem coordinateRotation_apply (n : ℕ) (i j k : Fin n) (v : EuclideanSpace ℝ (Fin n)) :
    coordinateRotation n i j v k=v (Equiv.swap i j k) := by
  simp [coordinateRotation,LinearIsometryEquiv.piLpCongrLeft_apply,Equiv.piCongrLeft']

omit [Fintype E] in
theorem freeSpinReference_rotation (n : ℕ) [NeZero n] (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving (SpinSystem.rotateConfiguration (fun _ : V => U)) (freeSpinReference n) (freeSpinReference n) :=
  measurePreserving_pi (fun _ : V => sphereProbability n) (fun _ => sphereProbability n)
    (fun _ => spinRotation_preserves_probability U)

omit [Fintype V] in
theorem freeSpinEnergy_rotation (n : ℕ) (left right : E → V) (b : E → ℝ)
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (s : V → Spin n) :
    freeSpinEnergy n left right b (SpinSystem.rotateConfiguration (fun _ : V => U) s)=
      freeSpinEnergy n left right b s := by
  apply Finset.sum_congr rfl
  intro e _
  change b e*⟪U (s (left e)).val,U (s (right e)).val⟫_ℝ=_
  rw [U.inner_map_map]

omit [Fintype V] [Fintype E] in
theorem continuous_coordinateSpinProduct (n : ℕ) (i : Fin n) (x y : V) :
    Continuous (coordinateSpinProduct n i x y) := by
  unfold coordinateSpinProduct
  fun_prop

theorem coordinateSpinMean_eq (n : ℕ) [NeZero n] (left right : E → V) (b : E → ℝ) (i j : Fin n) (x y : V) :
    freeSpinMean n left right b (coordinateSpinProduct n i x y)=
      freeSpinMean n left right b (coordinateSpinProduct n j x y) := by
  let U := coordinateRotation n i j
  have he (s : V → Spin n) :
      coordinateSpinProduct n i x y (SpinSystem.rotateConfiguration (fun _ : V => U) s)=
        coordinateSpinProduct n j x y s := by
    change (U (s x).val) i*(U (s y).val) i=_
    simp only [U,coordinateRotation_apply,Equiv.swap_apply_left,coordinateSpinProduct]
  have hi := (freeSpinReference_rotation (V := V) n U).integral_comp
    (SpinSystem.rotateConfiguration (fun _ : V => U)).measurableEmbedding
    (fun s => Real.exp (freeSpinEnergy n left right b s)*coordinateSpinProduct n i x y s)
  simp_rw [freeSpinEnergy_rotation,he] at hi
  unfold freeSpinMean weightedMean
  rw [hi]

theorem innerSpinMean_eq_coordinate (n : ℕ) [NeZero n] (left right : E → V) (b : E → ℝ)
    (i : Fin n) (x y : V) :
    freeSpinMean n left right b (fun s => ⟪(s x).val,(s y).val⟫_ℝ)=
      n*freeSpinMean n left right b (coordinateSpinProduct n i x y) := by
  have he (s : V → Spin n) : ⟪(s x).val,(s y).val⟫_ℝ=
      ∑ j : Fin n,coordinateSpinProduct n j x y s := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct,coordinateSpinProduct,star_trivial]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hh : freeSpinMean n left right b (fun s => ⟪(s x).val,(s y).val⟫_ℝ)=
      ∑ j : Fin n,freeSpinMean n left right b (coordinateSpinProduct n j x y) := by
    unfold freeSpinMean weightedMean
    simp_rw [he,Finset.mul_sum]
    rw [integral_finsetSum]
    · rw [Finset.sum_div]
    · intro j _
      exact compact_integrable ((continuous_freeSpinEnergy _ _ _ _).rexp.mul
        (continuous_coordinateSpinProduct _ _ _ _))
  rw [hh]
  simp_rw [coordinateSpinMean_eq n left right b _ i x y]
  simp

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.OrthogonalAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace ClassicalON

theorem continuous_orthogonalSpin (n : ℕ) :
    Continuous (Function.uncurry (orthogonalSpin (n := n))) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp continuous_fst).clm_apply (continuous_subtype_val.comp continuous_snd)

theorem orthogonalSpin_transitive {n : ℕ} (s t : Spin n) :
    ∃ Q : SpinOrthogonal n,orthogonalSpin Q s=t := by
  let R := (Submodule.span ℝ {s.val-t.val})ᗮ.reflection
  refine ⟨Unitary.linearIsometryEquiv.symm R,?_⟩
  apply Subtype.ext
  change (Unitary.linearIsometryEquiv (Unitary.linearIsometryEquiv.symm R)) s.val=t.val
  rw [MulEquiv.apply_symm_apply]
  exact Submodule.reflection_sub (by rw [spin_norm,spin_norm])

theorem orthogonalSpin_preserves {n : ℕ} (Q : SpinOrthogonal n) :
    MeasurePreserving (orthogonalSpin Q) (sphereProbability n) (sphereProbability n) :=
  spinRotation_preserves_probability _

theorem integral_orthogonalSpin_eq {n : ℕ} [NeZero n] (f : Spin n → ℝ)
    (hf : Continuous f) (s : Spin n) :
    (∫ Q, f (orthogonalSpin Q s) ∂orthogonalLaw n)=∫ t,f t ∂sphereProbability n := by
  have he (t : Spin n) : (∫ Q,f (orthogonalSpin Q t) ∂orthogonalLaw n)=
      ∫ Q,f (orthogonalSpin Q s) ∂orthogonalLaw n := by
    obtain ⟨R,rfl⟩ := orthogonalSpin_transitive s t
    simp_rw [← orthogonalSpin_mul]
    exact integral_mul_right_eq_self (fun Q => f (orthogonalSpin Q s)) R
  have hh := integral_integral_swap (μ := sphereProbability n) (ν := orthogonalLaw n)
    (f := fun t Q => f (orthogonalSpin Q t)) (compact_integrable (show Continuous (fun p : Spin n×SpinOrthogonal n => f (orthogonalSpin p.2 p.1)) from
      hf.comp ((continuous_orthogonalSpin n).comp continuous_swap)))
  simp_rw [he] at hh
  rw [integral_const,probReal_univ,one_smul] at hh
  have hp (Q : SpinOrthogonal n) : (∫ t,f (orthogonalSpin Q t) ∂sphereProbability n)=∫ t,f t ∂sphereProbability n :=
    (orthogonalSpin_preserves Q).integral_comp (spinRotation (Unitary.linearIsometryEquiv Q)).measurableEmbedding f
  simp_rw [hp] at hh
  simpa using hh

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.BlockGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped InnerProductSpace Classical
namespace ClassicalON

theorem blockRadius_le_one (k : ℕ) (s : Spin (3+k)) : blockRadius k s≤1 := by
  have h := WithLp.norm_fst_le _ (splitThree k s.val)
  simpa only [blockRadius,blockHead,LinearIsometryEquiv.norm_map,spin_norm] using h

theorem block_inner (k : ℕ) (s t : Spin (3+k)) :
    ⟪s.val,t.val⟫_ℝ=⟪blockHead k s,blockHead k t⟫_ℝ+⟪blockTail k s,blockTail k t⟫_ℝ := by
  rw [← (splitThree k).inner_map_map]
  rfl

theorem blockHead_first (k : ℕ) (s : Spin (3+k)) : (blockHead k s) 0=s.val ⟨0,by omega⟩ := rfl

theorem continuous_blockHead (k : ℕ) : Continuous (blockHead k) :=
  (WithLp.continuous_fst _ _ _).comp ((splitThree k).continuous.comp continuous_subtype_val)
theorem continuous_blockTail (k : ℕ) : Continuous (blockTail k) :=
  (WithLp.continuous_snd _ _ _).comp ((splitThree k).continuous.comp continuous_subtype_val)
theorem continuous_blockRadius (k : ℕ) : Continuous (blockRadius k) := (continuous_blockHead k).norm

theorem block_head_direction (k : ℕ) (s : Spin (3+k)) :
    blockRadius k s • (blockDirection k s).val=blockHead k s := by
  unfold blockDirection
  split_ifs with h
  · simp only [blockRadius,h,norm_zero,zero_smul]
  · have hn : blockRadius k s ≠ 0 := norm_ne_zero_iff.mpr h
    simp only [smul_smul,mul_inv_cancel₀ hn,one_smul]

theorem blockFiber_inner (k : ℕ) (s q : Spin (3+k)) (t u : Spin 3) :
    ⟪(blockFiber k s t).val,(blockFiber k q u).val⟫_ℝ=
      blockRadius k s*blockRadius k q*⟪t.val,u.val⟫_ℝ+⟪blockTail k s,blockTail k q⟫_ℝ := by
  rw [block_inner,blockHead_fiber,blockHead_fiber,blockTail_fiber,blockTail_fiber]
  simp only [real_inner_smul_left,real_inner_smul_right]
  ring

theorem continuous_blockFiber (k : ℕ) : Continuous (Function.uncurry (blockFiber k)) := by
  apply Continuous.subtype_mk
  apply (splitThree k).symm.continuous.comp
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.continuous.comp
    ((((continuous_blockRadius k).comp continuous_fst).smul (continuous_subtype_val.comp continuous_snd)).prodMk
      ((continuous_blockTail k).comp continuous_fst))

theorem blockRotateSpin_fiber (k : ℕ) (Q : SpinOrthogonal 3) (s : Spin (3+k)) :
    blockRotateSpin k Q s=blockFiber k s (orthogonalSpin Q (blockDirection k s)) := by
  apply Subtype.ext
  apply (splitThree k).injective
  change splitThree k ((splitThree k).symm _)=splitThree k ((splitThree k).symm _)
  simp only [LinearIsometryEquiv.apply_symm_apply]
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext
  · change (Unitary.linearIsometryEquiv Q) (blockHead k s)=
      blockRadius k s • ((Unitary.linearIsometryEquiv Q) (blockDirection k s).val)
    rw [← map_smul,block_head_direction]
  · rfl

theorem continuous_blockRotateSpin (k : ℕ) : Continuous (Function.uncurry (blockRotateSpin k)) := by
  apply Continuous.subtype_mk
  change Continuous (fun p : SpinOrthogonal 3×Spin (3+k) =>
    (splitThree k).symm (WithLp.toLp 2 (((p.1:SpinOperator 3) (blockHead k p.2)),blockTail k p.2)))
  apply (splitThree k).symm.continuous.comp
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.continuous.comp
  exact ((continuous_subtype_val.comp continuous_fst).clm_apply ((continuous_blockHead k).comp continuous_snd)).prodMk
    ((continuous_blockTail k).comp continuous_snd)

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.BlockOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV

noncomputable section
open MeasureTheory
open scoped InnerProductSpace Classical
namespace ClassicalON

theorem orthogonalSpin_eval_preserves (n : ℕ) [NeZero n] (s : Spin n) :
    MeasurePreserving (fun Q : SpinOrthogonal n => orthogonalSpin Q s)
      (orthogonalLaw n) (sphereProbability n) := by
  have hc : Continuous (fun Q : SpinOrthogonal n => orthogonalSpin Q s) :=
    (continuous_orthogonalSpin n).comp (continuous_id.prodMk continuous_const)
  refine ⟨hc.measurable,?_⟩
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [integral_map (f := fun x => f x) hc.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  exact integral_orthogonalSpin_eq f f.continuous s

variable {V : Type uV} [Fintype V]

omit [Fintype V] in
theorem continuous_blockFiberConfiguration (k : ℕ) :
    Continuous (Function.uncurry (blockFiberConfiguration (V := V) k)) := by
  apply continuous_pi
  intro v
  exact (continuous_blockFiber k).comp
    (f := fun p : (V → Spin (3+k))×(V → Spin 3) => (p.1 v,p.2 v))
    (((continuous_apply v).comp continuous_fst).prodMk ((continuous_apply v).comp continuous_snd))

omit [Fintype V] in
theorem blockRotateConfiguration_fiber (k : ℕ) (Q : V → SpinOrthogonal 3) (s : V → Spin (3+k)) :
    blockRotateConfiguration k Q s=
      blockFiberConfiguration k s (fun v => orthogonalSpin (Q v) (blockDirection k (s v))) := by
  funext v
  exact blockRotateSpin_fiber k (Q v) (s v)

omit [Fintype V] in
theorem continuous_blockRotateConfiguration (k : ℕ) : Continuous
    (fun p : (V → SpinOrthogonal 3)×(V → Spin (3+k)) => blockRotateConfiguration k p.1 p.2) := by
  apply continuous_pi
  intro v
  exact (continuous_blockRotateSpin k).comp
    (f := fun p : (V → SpinOrthogonal 3)×(V → Spin (3+k)) => (p.1 v,p.2 v))
    (((continuous_apply v).comp continuous_fst).prodMk ((continuous_apply v).comp continuous_snd))

theorem blockRotateConfiguration_preserves (k : ℕ) (Q : V → SpinOrthogonal 3) :
    MeasurePreserving (blockRotateConfiguration k Q) (freeSpinReference (3+k)) (freeSpinReference (3+k)) :=
  measurePreserving_pi (fun _ : V => sphereProbability (3+k)) (fun _ => sphereProbability (3+k))
    (fun v => spinRotation_preserves_probability (blockRotation k (Q v)))

theorem integral_block_orbit (k : ℕ) (f : (V → Spin (3+k)) → ℝ) (hf : Continuous f)
    (s : V → Spin (3+k)) :
    (∫ Q,f (blockRotateConfiguration k Q s) ∂orthogonalConfigurationLaw)=
      ∫ t,f (blockFiberConfiguration k s t) ∂freeSpinReference 3 := by
  have hp := measurePreserving_pi (fun _ : V => orthogonalLaw 3) (fun _ => sphereProbability 3)
    (fun v => orthogonalSpin_eval_preserves 3 (blockDirection k (s v)))
  have hc : Continuous (fun t : V → Spin 3 => f (blockFiberConfiguration k s t)) :=
    hf.comp ((continuous_blockFiberConfiguration k).comp
      (f := fun t : V → Spin 3 => (s,t)) (continuous_const.prodMk continuous_id))
  rw [show freeSpinReference (V := V) 3=
      (orthogonalConfigurationLaw (V := V)).map
        (fun Q v => orthogonalSpin (Q v) (blockDirection k (s v))) from hp.map_eq.symm,
    integral_map hp.measurable.aemeasurable hc.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards with Q
  rw [blockRotateConfiguration_fiber]

theorem integral_freeSpinReference_block (k : ℕ) (f : (V → Spin (3+k)) → ℝ) (hf : Continuous f) :
    (∫ s,f s ∂freeSpinReference (3+k))=
      ∫ s,∫ t,f (blockFiberConfiguration k s t) ∂freeSpinReference 3 ∂freeSpinReference (3+k) := by
  let : NeZero (3+k) := ⟨by omega⟩
  have hc : Continuous (fun p : (V → Spin (3+k))×(V → SpinOrthogonal 3) =>
      f (blockRotateConfiguration k p.2 p.1)) :=
    hf.comp ((continuous_blockRotateConfiguration k).comp
      (f := (Prod.swap : (V → Spin (3+k))×(V → SpinOrthogonal 3) →
        (V → SpinOrthogonal 3)×(V → Spin (3+k)))) continuous_swap)
  have he := integral_integral_swap (μ := freeSpinReference (3+k)) (ν := orthogonalConfigurationLaw)
    (f := fun s Q => f (blockRotateConfiguration k Q s)) (compact_integrable hc)
  have hi (Q : V → SpinOrthogonal 3) :
      (∫ s,f (blockRotateConfiguration k Q s) ∂freeSpinReference (3+k))=∫ s,f s ∂freeSpinReference (3+k) :=
    (blockRotateConfiguration_preserves k Q).integral_comp
      (blockRotateConfiguration k Q).measurableEmbedding f
  simp_rw [hi] at he
  simp only [integral_const,probReal_univ,one_smul] at he
  rw [← he]
  exact integral_congr_ae (Filter.Eventually.of_forall (integral_block_orbit k f hf))

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.BlockKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped InnerProductSpace BigOperators Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in
theorem blockCoupling_bounds (k : ℕ) (left right : E → V) (b : E → ℝ) (hb : ∀ e,0 ≤ b e)
    (s : V → Spin (3+k)) (e : E) : 0 ≤ blockCoupling k left right b s e ∧ blockCoupling k left right b s e ≤ b e := by
  unfold blockCoupling
  constructor
  · exact mul_nonneg (mul_nonneg (hb e) (blockRadius_nonneg _ _)) (blockRadius_nonneg _ _)
  · calc
      _ ≤ b e*1*1 := mul_le_mul (mul_le_mul_of_nonneg_left (blockRadius_le_one _ _) (hb e))
        (blockRadius_le_one _ _) (blockRadius_nonneg _ _) (by simpa using hb e)
      _ = b e := by ring

omit [Fintype V] in
theorem blockFiberConfiguration_energy (k : ℕ) (left right : E → V) (b : E → ℝ)
    (s : V → Spin (3+k)) (t : V → Spin 3) :
    freeSpinEnergy (3+k) left right b (blockFiberConfiguration k s t)=
      freeSpinEnergy 3 left right (blockCoupling k left right b s) t+blockTailEnergy k left right b s := by
  unfold freeSpinEnergy blockTailEnergy blockFiberConfiguration
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [blockFiber_inner]
  unfold blockCoupling
  ring

omit [Fintype V] [Fintype E] in
theorem blockFiberConfiguration_first (k : ℕ) (x y : V) (s : V → Spin (3+k)) (t : V → Spin 3) :
    coordinateSpinProduct (3+k) ⟨0,by omega⟩ x y (blockFiberConfiguration k s t)=
      (blockRadius k (s x)*blockRadius k (s y))*firstSpinProduct x y t := by
  unfold coordinateSpinProduct blockFiberConfiguration
  rw [← blockHead_first,← blockHead_first,blockHead_fiber,blockHead_fiber]
  simp only [PiLp.smul_apply,smul_eq_mul,firstSpinProduct]
  ring

theorem freeSpinPartition_pos (n : ℕ) [NeZero n] (left right : E → V) (b : E → ℝ) :
    0 < freeSpinPartition n left right b :=
  compact_integral_pos (continuous_freeSpinEnergy _ _ _ _).rexp (fun _ => Real.exp_pos _)

theorem block_fiber_partition (k : ℕ) (left right : E → V) (b : E → ℝ) (s : V → Spin (3+k)) :
    (∫ t,Real.exp (freeSpinEnergy (3+k) left right b (blockFiberConfiguration k s t)) ∂freeSpinReference 3)=
      Real.exp (blockTailEnergy k left right b s)*freeSpinPartition 3 left right (blockCoupling k left right b s) := by
  simp_rw [blockFiberConfiguration_energy,Real.exp_add]
  rw [integral_mul_const]
  exact mul_comm _ _

theorem block_fiber_numerator (k : ℕ) (left right : E → V) (b : E → ℝ)
    (x y : V) (s : V → Spin (3+k)) :
    (∫ t,Real.exp (freeSpinEnergy (3+k) left right b (blockFiberConfiguration k s t))*
      coordinateSpinProduct (3+k) ⟨0,by omega⟩ x y (blockFiberConfiguration k s t) ∂freeSpinReference 3)=
      (Real.exp (blockTailEnergy k left right b s)*freeSpinPartition 3 left right (blockCoupling k left right b s))*
        ((blockRadius k (s x)*blockRadius k (s y))*
          freeSpinMean 3 left right (blockCoupling k left right b s) (firstSpinProduct x y)) := by
  have hz := (freeSpinPartition_pos 3 left right (blockCoupling k left right b s)).ne'
  simp_rw [blockFiberConfiguration_energy,Real.exp_add,blockFiberConfiguration_first]
  have he (t : V → Spin 3) :
      Real.exp (freeSpinEnergy 3 left right (blockCoupling k left right b s) t)*
        Real.exp (blockTailEnergy k left right b s)*
          (blockRadius k (s x)*blockRadius k (s y)*firstSpinProduct x y t)=
      (Real.exp (blockTailEnergy k left right b s)*(blockRadius k (s x)*blockRadius k (s y)))*
        (Real.exp (freeSpinEnergy 3 left right (blockCoupling k left right b s) t)*firstSpinProduct x y t) := by ring
  simp_rw [he]
  rw [integral_const_mul]
  unfold freeSpinMean weightedMean
  change _=(_*freeSpinPartition 3 left right (blockCoupling k left right b s))*
    (_*(_/freeSpinPartition 3 left right (blockCoupling k left right b s)))
  field_simp

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.BlockReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped InnerProductSpace BigOperators Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

theorem coordinateSpinMean_block_bounds (k : ℕ) (left right : E → V) (b : E → ℝ)
    (hb : ∀ e,0 ≤ b e) (x y : V) (C : ℝ)
    (hthree : ∀ c : E → ℝ,(∀ e,0 ≤ c e ∧ c e ≤ b e) →
      0 ≤ freeSpinMean 3 left right c (firstSpinProduct x y) ∧
        freeSpinMean 3 left right c (firstSpinProduct x y) ≤ C) :
    0 ≤ freeSpinMean (3+k) left right b (coordinateSpinProduct (3+k) ⟨0,by omega⟩ x y) ∧
      freeSpinMean (3+k) left right b (coordinateSpinProduct (3+k) ⟨0,by omega⟩ x y) ≤ C := by
  let : NeZero (3+k) := ⟨by omega⟩
  let W : (V → Spin (3+k)) → ℝ := fun s => Real.exp (freeSpinEnergy (3+k) left right b s)
  let F := coordinateSpinProduct (3+k) ⟨0,by omega⟩ x y
  have hW : Continuous W := (continuous_freeSpinEnergy _ _ _ _).rexp
  have hF : Continuous F := continuous_coordinateSpinProduct _ _ _ _
  have hWF : Continuous (fun s => W s*F s) := hW.mul hF
  have hpoint (s : V → Spin (3+k)) :
      0 ≤ (∫ t,W (blockFiberConfiguration k s t)*F (blockFiberConfiguration k s t) ∂freeSpinReference 3) ∧
      (∫ t,W (blockFiberConfiguration k s t)*F (blockFiberConfiguration k s t) ∂freeSpinReference 3) ≤
        C*(∫ t,W (blockFiberConfiguration k s t) ∂freeSpinReference 3) := by
    dsimp only [W,F]
    rw [block_fiber_numerator,block_fiber_partition]
    have h3 := hthree (blockCoupling k left right b s) (blockCoupling_bounds k left right b hb s)
    have hr0 : 0 ≤ blockRadius k (s x)*blockRadius k (s y) :=
      mul_nonneg (blockRadius_nonneg _ _) (blockRadius_nonneg _ _)
    have hr1 : blockRadius k (s x)*blockRadius k (s y) ≤ 1 :=
      (mul_le_of_le_one_left (blockRadius_nonneg _ _) (blockRadius_le_one _ _)).trans
        (blockRadius_le_one _ _)
    have hD : 0 ≤ Real.exp (blockTailEnergy k left right b s)*
        freeSpinPartition 3 left right (blockCoupling k left right b s) :=
      mul_nonneg (Real.exp_pos _).le (freeSpinPartition_pos _ _ _ _).le
    constructor
    · exact mul_nonneg hD (mul_nonneg hr0 h3.1)
    · calc
        _ ≤ (Real.exp (blockTailEnergy k left right b s)*
            freeSpinPartition 3 left right (blockCoupling k left right b s))*C :=
          mul_le_mul_of_nonneg_left
            ((mul_le_of_le_one_left h3.1 hr1).trans h3.2) hD
        _ = _ := mul_comm _ _
  have hNi : Integrable (fun s : V → Spin (3+k) =>
      ∫ t,W (blockFiberConfiguration k s t)*F (blockFiberConfiguration k s t) ∂freeSpinReference 3)
        (freeSpinReference (3+k)) :=
    compact_integrable (compact_parametric_integral _
      (hWF.comp (continuous_blockFiberConfiguration k)))
  have hDi : Integrable (fun s : V → Spin (3+k) =>
      ∫ t,W (blockFiberConfiguration k s t) ∂freeSpinReference 3) (freeSpinReference (3+k)) :=
    compact_integrable (compact_parametric_integral _
      (hW.comp (continuous_blockFiberConfiguration k)))
  have hN : 0 ≤ ∫ s,W s*F s ∂freeSpinReference (3+k) := by
    rw [integral_freeSpinReference_block k _ hWF]
    exact integral_nonneg (fun s => (hpoint s).1)
  have hND : (∫ s,W s*F s ∂freeSpinReference (3+k)) ≤ C*(∫ s,W s ∂freeSpinReference (3+k)) := by
    rw [integral_freeSpinReference_block k _ hWF,integral_freeSpinReference_block k _ hW,← integral_const_mul]
    exact integral_mono hNi (hDi.const_mul C) (fun s => (hpoint s).2)
  have hD : 0 < ∫ s,W s ∂freeSpinReference (3+k) :=
    compact_integral_pos hW (fun _ => Real.exp_pos _)
  constructor
  · exact div_nonneg hN hD.le
  · exact (div_le_iff₀ hD).mpr hND

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped InnerProductSpace BigOperators Classical
namespace ClassicalON

theorem correlation_eq_freeSpinMean (n : ℕ) (G : LatticeGraph) (b : G.edges → ℝ) (x y : G.vertices) :
    correlation n G b x y=freeSpinMean n (fun e : G.edges => e.val.1) (fun e => e.val.2) b
      (fun s => ⟪(s x).val,(s y).val⟫_ℝ) := by
  unfold correlation partition interaction referenceLaw freeSpinMean weightedMean freeSpinEnergy freeSpinReference
  congr 1
  apply integral_congr_ae
  filter_upwards with s
  exact mul_comm _ _

theorem main_oai : ExponentialDecay := by
  intro n hn β hβ
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  let : NeZero (3+k) := ⟨by omega⟩
  obtain ⟨m,hm,hexp⟩ := LatticeGraph.connection_exponential β hβ.le
  refine ⟨(3+k:ℕ)*4,m,hm,?_⟩
  intro G b hb x y
  have hthree (c : G.edges → ℝ) (hc : ∀ e,0 ≤ c e ∧ c e ≤ b e) :
      0 ≤ freeSpinMean 3 (fun e : G.edges => e.val.1) (fun e => e.val.2) c (firstSpinProduct x y) ∧
      freeSpinMean 3 (fun e : G.edges => e.val.1) (fun e => e.val.2) c (firstSpinProduct x y) ≤
        4*Real.exp (-m*siteDistance x.val y.val) := by
    have hfirst := firstSpinMean_bounds (fun e : G.edges => e.val.1) (fun e => e.val.2) c
      (fun e => (hc e).1) x y
    exact ⟨hfirst.1,hfirst.2.trans (hexp G c (fun e => ⟨(hc e).1,(hc e).2.trans (hb e).2⟩) x y)⟩
  have hbound := coordinateSpinMean_block_bounds k (fun e : G.edges => e.val.1) (fun e => e.val.2) b
    (fun e => (hb e).1) x y (4*Real.exp (-m*siteDistance x.val y.val)) hthree
  rw [correlation_eq_freeSpinMean,innerSpinMean_eq_coordinate (3+k)
    (fun e : G.edges => e.val.1) (fun e => e.val.2) b ⟨0,by omega⟩ x y]
  constructor
  · exact mul_nonneg (Nat.cast_nonneg _) hbound.1
  · calc
      _ ≤ (3+k:ℕ)*(4*Real.exp (-m*siteDistance x.val y.val)) :=
        mul_le_mul_of_nonneg_left hbound.2 (Nat.cast_nonneg _)
      _ = _ := by ring

end ClassicalON

end

end OAI
end

theorem solution : type_of% @OAI.ClassicalON.main_oai := @OAI.ClassicalON.main_oai

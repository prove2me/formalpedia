-- Prove2me | solution 1 for OAI.Kadison.RepresentedTower.exists_tower_average
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:07:10.215568+00:00
-- url     : https://prove2.me/submissions/adb9a961-fdbe-489c-be2a-fe81e293949a

import Mathlib
import Definitions.Def_OAIQ039C003
import Definitions.Def_OAIQ039C019
import Definitions.Def_OAIQ039C030
import Theorems.Thm_OAI_Kadison_CompactAverage_exists_average

section
-- module Solutions.OAIQ039_CM.Commutator_Average
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace

open MeasureTheory Filter

namespace Kadison.WeakOperatorIntegral

variable {ι H : Type*} [MeasurableSpace ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (μ : Measure ι) [IsProbabilityMeasure μ] (T : ι → H →L[ℂ] H)
  (hI : ∀ x y, Integrable (fun i => inner ℂ (T i x) y) μ)
  (V : H →L[ℂ] H)
  (hV : ∀ x y, inner ℂ (V x) y = ∫ i, inner ℂ (T i x) y ∂μ)

omit [CompleteSpace H] in
include hV in
lemma norm_le_of_integral {C : ℝ} (hC : 0 ≤ C) (hT : ∀ i, ‖T i‖ ≤ C) : ‖V‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound V hC
  intro x
  have hi : ‖inner ℂ (V x) (V x)‖ ≤ C*‖x‖*‖V x‖ := by
    rw [hV]
    have h := norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun i => inner ℂ (T i x) (V x)) (C := C*‖x‖*‖V x‖)
      (Eventually.of_forall (fun i => (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (((T i).le_opNorm x).trans
          (mul_le_mul_of_nonneg_right (hT i) (norm_nonneg x))) (norm_nonneg _))))
    simpa only [probReal_univ,mul_one] using h
  rw [← inner_self_re_eq_norm,inner_self_eq_norm_mul_norm] at hi
  by_cases hv : ‖V x‖=0
  · rw [hv]; positivity
  · have hp : 0 < ‖V x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
    exact (mul_le_mul_iff_left₀ hp).mp (by simpa [mul_comm,mul_left_comm,mul_assoc] using hi)

end Kadison.WeakOperatorIntegral

namespace Kadison.WeakOperatorIntegral

open MeasureTheory Filter

variable {ι H : Type*} [MeasurableSpace ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (μ : Measure ι) [IsProbabilityMeasure μ] (T : ι → H →L[ℂ] H)
  (hI : ∀ x y, Integrable (fun i => inner ℂ (T i x) y) μ)
  (V : H →L[ℂ] H)
  (hV : ∀ x y, inner ℂ (V x) y = ∫ i, inner ℂ (T i x) y ∂μ)

omit [CompleteSpace H] in
include hI hV in
lemma difference_coeff (W : H →L[ℂ] H) (x y : H) :
    inner ℂ ((V-W) x) y = ∫ i, inner ℂ ((T i-W) x) y ∂μ := by
  simp only [sub_apply,inner_sub_left]
  rw [hV,integral_sub (hI x y) (integrable_const _)]
  simp only [integral_const,MeasureTheory.probReal_univ,one_smul]

omit [CompleteSpace H] in
include hI hV in
lemma difference_norm (W : H →L[ℂ] H) {C : ℝ} (hC : 0≤C)
    (hb : ∀ i, ‖T i-W‖≤C) : ‖V-W‖≤C :=
  norm_le_of_integral μ (fun i => T i-W) (V-W) (difference_coeff μ T hI V hV W) hC hb

end Kadison.WeakOperatorIntegral

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_StrongContinuity
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology

open Filter

namespace Kadison.StrongContinuity

variable {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℂ E]

variable (T : X → E →ₗᵢ[ℂ] E)

lemma joint (h : ∀ x, Continuous fun g => T g x) : Continuous (fun p : X × E => T p.1 p.2) := by
  apply continuous_prod_of_continuous_lipschitzWith' _ 1
  · intro g
    exact (T g).isometry.lipschitz
  · exact h

end Kadison.StrongContinuity

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CompactAverage
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace

open MeasureTheory MeasureTheory.Measure

namespace Kadison.CompactAverage

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (U : G →* (H ≃ₗᵢ[ℂ] H)) (hU : ∀ x : H, Continuous fun g => U g x)

variable (Y : H →L[ℂ] H)

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
include hU in
lemma conjugate_continuous (x : H) : Continuous fun g => conjugate U Y g x := by
  have hi : Continuous fun g => (U g).symm x := by
    simpa only [Function.comp_def, map_inv,LinearIsometryEquiv.coe_inv] using (hU x).comp continuous_inv
  have hj := StrongContinuity.joint (fun g => (U g).toLinearIsometry) hU
  exact hj.comp (continuous_id.prodMk (Y.continuous.comp hi))

end Kadison.CompactAverage

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_WeakOperatorLimit
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace

open Filter

namespace Kadison.WeakOperatorLimit

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem norm_le_of_tendsto {l : Filter ι} [l.NeBot] {T : ι → E →L[ℂ] F}
    {V : E →L[ℂ] F} (hlim : ∀ x y, Tendsto (fun i => inner ℂ (T i x) y) l
      (𝓝 (inner ℂ (V x) y))) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ᶠ i in l, ‖T i‖ ≤ C) : ‖V‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound V hC
  intro x
  have hi : ‖inner ℂ (V x) (V x)‖ ≤ C*‖x‖*‖V x‖ := by
    apply le_of_tendsto (hlim x (V x)).norm
    filter_upwards [hT] with i hi
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (((T i).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right hi (norm_nonneg x))) (norm_nonneg _))
  rw [← inner_self_re_eq_norm,inner_self_eq_norm_mul_norm] at hi
  by_cases hv : ‖V x‖=0
  · rw [hv]; positivity
  · have hp : 0 < ‖V x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
    exact (mul_le_mul_iff_left₀ hp).mp (by simpa [pow_two,mul_comm,mul_left_comm,mul_assoc] using hi)

end Kadison.WeakOperatorLimit

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_WeakConvergence
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace

open Filter

namespace Kadison.WeakOperatorLimit

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable {l : Filter ι} {T : ι → H →L[ℂ] H} {V : H →L[ℂ] H}

lemma Converges.sub {S : ι → H →L[ℂ] H} {W : H →L[ℂ] H}
    (hT : Converges T V l) (hS : Converges S W l) : Converges (T-S) (V-W) l := by
  intro x y
  simpa only [Pi.sub_apply,sub_apply,inner_sub_left] using (hT x y).sub (hS x y)

lemma converges_const (V : H →L[ℂ] H) : Converges (fun _ : ι => V) V l := fun _ _ => tendsto_const_nhds

lemma Converges.mul_right (hT : Converges T V l) (a : H →L[ℂ] H) :
    Converges (fun i => T i*a) (V*a) l := by
  intro x y
  exact hT (a x) y

lemma Converges.mul_left [CompleteSpace H] (hT : Converges T V l) (a : H →L[ℂ] H) :
    Converges (fun i => a*T i) (a*V) l := by
  intro x y
  simpa only [mul_apply_eq_comp,← ContinuousLinearMap.adjoint_inner_right a] using hT x (a.adjoint y)

lemma Converges.commutator [CompleteSpace H] (hT : Converges T V l) (a : H →L[ℂ] H) :
    Converges (fun i => T i*a-a*T i) (V*a-a*V) l :=
  (hT.mul_right a).sub (hT.mul_left a)

lemma Converges.unique [l.NeBot] {W : H →L[ℂ] H}
    (hT : Converges T V l) (hW : Converges T W l) : V=W := by
  ext x
  exact ext_inner_right ℂ (fun y => tendsto_nhds_unique (hT x y) (hW x y))

lemma Converges.eq_const [l.NeBot] (hT : Converges T V l) (W : H →L[ℂ] H)
    (hW : ∀ᶠ i in l, T i=W) : V=W := by
  apply hT.unique
  intro x y
  exact tendsto_const_nhds.congr' (hW.mono fun i h => by change inner ℂ (W x) y = inner ℂ (T i x) y; rw [h])

lemma Converges.norm [l.NeBot] (hT : Converges T V l) {C : ℝ} (hC : 0≤C)
    (hb : ∀ᶠ i in l, ‖T i‖≤C) : ‖V‖≤C := norm_le_of_tendsto hT hC hb

lemma Converges.commutes [CompleteSpace H] [l.NeBot] (hT : Converges T V l) (a : H →L[ℂ] H)
    (hb : ∀ᶠ i in l, T i*a=a*T i) : V*a=a*V := by
  apply sub_eq_zero.mp
  exact (hT.commutator a).eq_const 0 (hb.mono fun _ h => sub_eq_zero.mpr h)

lemma Converges.dist [l.NeBot] (hT : Converges T V l) (W : H →L[ℂ] H)
    {C : ℝ} (hC : 0≤C) (hb : ∀ᶠ i in l, ‖T i-W‖≤C) : ‖V-W‖≤C :=
  (hT.sub (converges_const W)).norm hC hb

end Kadison.WeakOperatorLimit

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_RepresentedTowerAverage
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Matrix.Norms.L2Operator Topology

open MeasureTheory Filter

namespace Kadison.RepresentedTower

variable {A K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))

lemma conjugate_distance (Y : K →L[ℂ] K) (u : unitary A) :
    ‖CompactAverage.conjugate (unitaryRepresentation ρ) Y u-Y‖=‖Y*ρ (u:A)-ρ (u:A)*Y‖ := by
  let w : unitary (K →L[ℂ] K) := ⟨ρ (u:A),Unitary.map_mem ρ u.property⟩
  have he : CompactAverage.conjugate (unitaryRepresentation ρ) Y u-Y=
      ((w:K →L[ℂ] K)*Y-Y*(w:K →L[ℂ] K))*star (w:K →L[ℂ] K) := by
    change (w:K →L[ℂ] K)*Y*star (w:K →L[ℂ] K)-Y=_
    rw [sub_mul,mul_assoc Y (w:K →L[ℂ] K) (star (w:K →L[ℂ] K)),w.property.2,mul_one]
  rw [he,CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem w.property),norm_sub_rev]

variable (I : ℕ → Type*) [∀ n,Fintype (I n)] [∀ n,DecidableEq (I n)] [∀ n,Nonempty (I n)]

variable (φ : ∀ n,Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)

omit [∀ (n : ℕ), Nonempty (I n)] in
lemma stageUnitary_continuous (n : ℕ) (x : K) :
    Continuous fun u => stageUnitaryRepresentation ρ I φ n u x := by
  change Continuous fun u : unitary (Matrix (I n) (I n) ℂ) => ρ (φ n (u:_)) x
  exact (((ρ.comp (φ n)).toLinearMap.continuous_of_finiteDimensional).comp
    continuous_subtype_val).clm_apply continuous_const

lemma exists_stage_average (Y : K →L[ℂ] K) {δ : ℝ} (hδ : 0≤δ)
    (hb : ∀ u : unitary A,‖Y*ρ (u:A)-ρ (u:A)*Y‖≤δ) (n : ℕ) :
    ∃ Z : K →L[ℂ] K,‖Z‖≤‖Y‖ ∧ ‖Z-Y‖≤δ ∧
      ∀ a,Z*ρ (φ n a)=ρ (φ n a)*Z := by
  classical
  let := UnitaryHaar.compactUnitary (Matrix (I n) (I n) ℂ)
  let : MeasurableSpace (unitary (Matrix (I n) (I n) ℂ)) := borel _
  let : BorelSpace (unitary (Matrix (I n) (I n) ℂ)) := ⟨rfl⟩
  let U := stageUnitaryRepresentation ρ I φ n
  let μ := UnitaryHaar.probability (unitary (Matrix (I n) (I n) ℂ))
  obtain ⟨Z,hZ,hcomm,hcoeff⟩ := CompactAverage.exists_average U (stageUnitary_continuous ρ I φ n) Y μ
  refine ⟨Z,hZ,?_,?_⟩
  · apply WeakOperatorIntegral.difference_norm μ (CompactAverage.conjugate U Y) _ Z hcoeff Y hδ
    · intro u
      exact (conjugate_distance ρ Y (stageUnitaryMap I φ n u)).le.trans (hb _)
    · intro x y
      exact ((CompactAverage.conjugate_continuous U (stageUnitary_continuous ρ I φ n) Y x).inner
        continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · let D : Matrix (I n) (I n) ℂ →ₗ[ℂ] (K →L[ℂ] K) :=
      { toFun := fun a => Z*ρ (φ n a)-ρ (φ n a)*Z
        map_add' := by intro a b; simp only [map_add,mul_add,add_mul]; abel
        map_smul' := by intro z a; simp only [map_smul,mul_smul_comm,smul_mul_assoc,smul_sub]; rfl }
    have hD : D=0 := by
      apply LinearMap.ext_on (CStarAlgebra.span_unitary (Matrix (I n) (I n) ℂ))
      intro u hu
      exact sub_eq_zero.mpr (hcomm ⟨u,hu⟩)
    intro a
    exact sub_eq_zero.mp (congrArg (fun D : Matrix (I n) (I n) ℂ →ₗ[ℂ] (K →L[ℂ] K) => D a) hD)

theorem exists_tower_average_oai (hφ : Monotone (fun n => (φ n).range))
    (Y : K →L[ℂ] K) {δ : ℝ} (hδ : 0≤δ)
    (hb : ∀ u : unitary A,‖Y*ρ (u:A)-ρ (u:A)*Y‖≤δ) :
    ∃ Z : K →L[ℂ] K,‖Z‖≤‖Y‖ ∧ ‖Z-Y‖≤δ ∧
      ∀ a : K →L[ℂ] K,a∈Set.centralizer (Set.centralizer
        ((iSup fun n => (ρ.comp (φ n)).range : StarSubalgebra ℂ (K →L[ℂ] K)) : Set (K →L[ℂ] K))) → Z*a=a*Z := by
  choose T hn hd hc using exists_stage_average ρ I φ Y hδ hb
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  obtain ⟨Z,hZ,hlim⟩ := WeakOperatorLimit.exists_ultralimit ω T ‖Y‖ (norm_nonneg Y) hn
  have hconv : WeakOperatorLimit.Converges T Z (ω:Filter ℕ) := hlim
  refine ⟨Z,hZ,hconv.dist Y hδ (Eventually.of_forall hd),?_⟩
  have hstage (n : ℕ) (a : Matrix (I n) (I n) ℂ) : Z*ρ (φ n a)=ρ (φ n a)*Z := by
    apply hconv.commutes
    apply (Ultrafilter.of_le atTop)
    filter_upwards [eventually_ge_atTop n] with m hm
    obtain ⟨b,hb⟩ := hφ hm (show φ n a∈(φ n).range from ⟨a,rfl⟩)
    rw [←hb]
    exact hc m b
  have hcent : Z∈Set.centralizer ((iSup fun n => (ρ.comp (φ n)).range : StarSubalgebra ℂ (K →L[ℂ] K)) : Set (K →L[ℂ] K)) := by
    have hcomm : (iSup fun n => (ρ.comp (φ n)).range)≤StarSubalgebra.centralizer ℂ ({Z} : Set (K →L[ℂ] K)) := by
      apply iSup_le
      intro n
      rintro a ⟨b,rfl⟩
      rw [StarSubalgebra.mem_centralizer_iff]
      intro z hz
      have he : z=Z := Set.mem_singleton_iff.mp hz
      subst z
      constructor
      · exact hstage n b
      · have hh := congrArg star (hstage n (star b))
        simpa only [star_mul,←map_star,star_star] using! hh.symm
    intro a ha
    exact (((StarSubalgebra.mem_centralizer_iff ℂ).mp (hcomm ha)) Z (Set.mem_singleton Z)).1.symm
  intro a ha
  exact ha Z hcent

end Kadison.RepresentedTower

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Kadison.RepresentedTower.exists_tower_average_oai.{u_1, u_2, u_3} := @OAI.Kadison.RepresentedTower.exists_tower_average_oai.{u_1, u_2, u_3}

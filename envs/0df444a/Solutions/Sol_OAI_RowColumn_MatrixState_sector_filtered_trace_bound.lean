-- Prove2me | solution 1 for OAI.RowColumn.MatrixState.sector_filtered_trace_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T02:03:39.972515+00:00
-- url     : https://prove2.me/submissions/f608af21-1a40-4425-9cea-616dcfcec957

import Mathlib
import Definitions.Def_OAIW2RC000

section
-- module Solutions.OAIW2_RowColumn.FiniteUnitary_Frames
attribute [-instance] _root_.OAI.RowColumn.FiniteStarAlgebra.algebraFiniteDimensional _root_.OAI.RowColumn.FiniteStarAlgebra.algebraIsClosed _root_.OAI.RowColumn.MatrixState.matrixAlgebraIsClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators ComplexConjugate

noncomputable section
open scoped RealInnerProductSpace
namespace RowColumn.UnitaryFrame
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma norm_minimizer_unique [CompleteSpace E] (K : Set E) (hK : Convex ℝ K)
    {x y : E} (hx : x ∈ K) (hy : y ∈ K)
    (hxm : ∀ z ∈ K, ‖x‖ ≤ ‖z‖) (hym : ∀ z ∈ K, ‖y‖ ≤ ‖z‖) : x = y := by
  have he : ‖x‖ = ‖y‖ := le_antisymm (hxm y hy) (hym x hx)
  have hm : (1/2 : ℝ) • x + (1/2 : ℝ) • y ∈ K :=
    hK hx hy (by norm_num) (by norm_num) (by norm_num)
  have hl := hxm _ hm
  have hn : ‖(1/2 : ℝ) • x + (1/2 : ℝ) • y‖ = (1/2 : ℝ)*‖x+y‖ := by
    rw [← smul_add, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
  rw [hn] at hl
  have hsq := mul_self_le_mul_self (norm_nonneg x) hl
  have hp := parallelogram_law_with_norm ℝ x y
  rw [← he] at hp
  have hd := sq_nonneg ‖x-y‖
  have hz : ‖x-y‖ = 0 := by
    nlinarith [norm_nonneg (x-y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- Simultaneous fixed point obtained from the unique minimum-norm point of a
closed convex invariant set. Applied to rank-one unitary frames, this replaces
Haar integration by finite-dimensional convex averaging. -/
theorem exists_fixed_minimum (K : Set E) (hne : K.Nonempty) (hclosed : IsClosed K)
    (hconv : Convex ℝ K) (L : ι → E →ₗᵢ[ℝ] E)
    (hL : ∀ i x, x ∈ K → L i x ∈ K) :
    ∃ x ∈ K, ∀ i, L i x = x := by
  obtain ⟨x,hx,hm⟩ := exists_norm_eq_iInf_of_complete_convex hne hclosed.isComplete hconv (0 : E)
  have hmin (z : E) (hz : z ∈ K) : ‖x‖ ≤ ‖z‖ := by
    have hh : (⨅ w : K, ‖(0 : E)-w‖) ≤ ‖(0 : E)-z‖ :=
      ciInf_le (f := fun w : K => ‖(0 : E) - (w : E)‖)
        ⟨0, Set.forall_mem_range.mpr (fun _ => norm_nonneg _)⟩ (⟨z,hz⟩ : K)
    rw [← hm] at hh
    simpa using hh
  refine ⟨x,hx,fun i => ?_⟩
  exact norm_minimizer_unique K hconv (hL i x hx) hx
    (fun z hz => by rw [(L i).norm_map]; exact hmin z hz) hmin

end RowColumn.UnitaryFrame

noncomputable section
open scoped BigOperators ComplexConjugate
namespace RowColumn.UnitaryFrame
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
lemma quadraticForm_real_smul [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) (c : ℝ) (x : E) :
    quadraticForm T (c • x) = c^2 * quadraticForm T x := by
  simp only [quadraticForm, ← Complex.coe_smul, map_smul, inner_smul_left,
    inner_smul_right, Complex.conj_ofReal]
  simp [Complex.mul_re, pow_two, mul_assoc]

lemma quadraticForm_continuous (T : E →ₗ[ℂ] E) : Continuous (quadraticForm T) :=
  Complex.continuous_re.comp (continuous_id.inner T.toContinuousLinearMap.continuous)

/-- Strict positivity of a finite-dimensional frame is uniformly coercive. -/
theorem positive_coercive (T : E →ₗ[ℂ] E)
    (hT : ∀ x : E, x ≠ 0 → 0 < quadraticForm T x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x, ε * ‖x‖^2 ≤ quadraticForm T x := by
  cases subsingleton_or_nontrivial E with
  | inl h =>
    let := h
    refine ⟨1, by norm_num, fun x => ?_⟩
    have he : x = 0 := Subsingleton.elim _ _
    simp [he, quadraticForm]
  | inr h =>
    let := h
    let : ProperSpace E := FiniteDimensional.proper ℂ E
    have hn : (Metric.sphere (0 : E) 1).Nonempty := NormedSpace.sphere_nonempty.mpr (by norm_num)
    obtain ⟨y,hy,hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn hn
      (quadraticForm_continuous T).continuousOn
    have hny : ‖y‖ = 1 := by simpa using hy
    have hpy : 0 < quadraticForm T y := hT y (by intro he; simp [he] at hny)
    refine ⟨quadraticForm T y, hpy, fun x => ?_⟩
    by_cases hx : x = 0
    · simp [hx, quadraticForm]
    · have hp : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hu : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : E) 1 := by
        simp [norm_smul, ne_of_gt hp]
      have hm : quadraticForm T y ≤ quadraticForm T (‖x‖⁻¹ • x) := hmin hu
      rw [quadraticForm_real_smul] at hm
      have hh := mul_le_mul_of_nonneg_right hm (sq_nonneg ‖x‖)
      calc
        _ ≤ (‖x‖⁻¹ ^ 2 * quadraticForm T x) * ‖x‖^2 := hh
        _ = _ := by field_simp [ne_of_gt hp]

end RowColumn.UnitaryFrame

namespace RowColumn.UnitaryFrame
open scoped BigOperators ComplexOrder ComplexConjugate
variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Group G]

attribute [local instance] OAI.RowColumn.UnitaryFrame.instNormedAddCommGroupLinearMapComplexId_solutions
lemma conjugation_apply (u : E ≃ₗᵢ[ℂ] E) (T : E →ₗ[ℂ] E) (x : E) :
    conjugationReal u T x = u (T (u.symm x)) := rfl

lemma conjugation_rankOne (u : E ≃ₗᵢ[ℂ] E) (x : E) :
    conjugationReal u (InnerProductSpace.rankOne ℂ x x).toLinearMap =
      (InnerProductSpace.rankOne ℂ (u x) (u x)).toLinearMap := by
  ext y
  change u (inner ℂ x (u.symm y) • x) = inner ℂ (u x) y • u x
  rw [map_smul]
  congr 1
  simpa only [u.apply_symm_apply] using (u.inner_map_map x (u.symm y)).symm

attribute [local instance] OAI.RowColumn.UnitaryFrame.instInnerProductSpaceRealLinearMapComplexId_solutions
lemma coerciveSet_closed (ε : ℝ) : IsClosed (coerciveSet (E := E) ε) := by
  rw [coerciveSet, Set.ofPred_forall]
  apply isClosed_iInter
  intro x
  exact isClosed_le continuous_const
    (show Continuous (fun T : E →ₗ[ℂ] E => quadraticForm T x) from
      (quadraticEval x).toContinuousLinearMap.continuous)

omit [FiniteDimensional ℂ E] in
lemma coerciveSet_convex [FiniteDimensional ℂ E] (ε : ℝ) :
    Convex ℝ (coerciveSet (E := E) ε) := by
  intro T hT V hV a b ha hb hab x
  have h₁ := mul_le_mul_of_nonneg_left (hT x) ha
  have h₂ := mul_le_mul_of_nonneg_left (hV x) hb
  change ε * ‖x‖^2 ≤ quadraticEval x (a • T + b • V)
  rw [map_add, map_smul, map_smul]
  change ε * ‖x‖^2 ≤ a * quadraticForm T x + b * quadraticForm V x
  calc
    ε * ‖x‖^2 = (a+b) * (ε * ‖x‖^2) := by rw [hab, one_mul]
    _ = a * (ε * ‖x‖^2) + b * (ε * ‖x‖^2) := add_mul _ _ _
    _ ≤ _ := add_le_add h₁ h₂

attribute [local instance] OAI.RowColumn.UnitaryFrame.instInnerProductSpaceComplexLinearMapId_solutions
lemma positiveSet_closed : IsClosed {T : E →ₗ[ℂ] E | T.IsPositive} := by
  have hs : IsClosed {T : E →ₗ[ℂ] E | T.IsSymmetric} := by
    have he : {T : E →ₗ[ℂ] E | T.IsSymmetric} =
        ⋂ x : E, ⋂ y : E,
        {T | starRingEnd ℂ (matrixEntry y x T) = matrixEntry x y T} := by
      ext T
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, matrixEntry, LinearMap.coe_mk,
        AddHom.coe_mk, inner_conj_symm, LinearMap.IsSymmetric]
    rw [he]
    exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq
      (Complex.continuous_conj.comp (matrixEntry y x).toContinuousLinearMap.continuous)
      (matrixEntry x y).toContinuousLinearMap.continuous
  have hn : IsClosed {T : E →ₗ[ℂ] E | ∀ x, 0 ≤ quadraticForm T x} := by
    rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro x
    exact isClosed_le continuous_const
      (show Continuous (fun T : E →ₗ[ℂ] E => quadraticForm T x) from
        (quadraticEval x).toContinuousLinearMap.continuous)
  have he : {T : E →ₗ[ℂ] E | T.IsPositive} =
      {T | T.IsSymmetric} ∩ {T | ∀ x, 0 ≤ quadraticForm T x} := by
    ext T
    constructor
    · intro h; exact ⟨h.isSymmetric, fun x => h.re_inner_nonneg_right x⟩
    · rintro ⟨hs,hn⟩
      refine ⟨hs, fun x => ?_⟩
      rw [inner_re_symm]
      exact hn x
  rw [he]
  exact hs.inter hn

omit [FiniteDimensional ℂ E] in
lemma positiveSet_convex [FiniteDimensional ℂ E] : Convex ℝ {T : E →ₗ[ℂ] E | T.IsPositive} := by
  intro T hT V hV a b ha hb hab
  change (a • T + b • V).IsPositive
  rw [← Complex.coe_smul a T, ← Complex.coe_smul b V]
  exact (hT.smul_of_nonneg (by exact_mod_cast ha)).add
    (hV.smul_of_nonneg (by exact_mod_cast hb))

lemma frameHull_invariant (π : G →* E ≃ₗᵢ[ℂ] E) (x₀ : E) (g : G) :
    Set.MapsTo (conjugationReal (π g)) (frameHull π x₀) (frameHull π x₀) := by
  apply Set.MapsTo.closure _ (conjugationReal (π g)).continuous
  rw [Set.mapsTo_iff_image_subset]
  rw [← LinearIsometry.coe_toLinearMap, (conjugationReal (π g)).toLinearMap.image_convexHull]
  apply convexHull_mono
  rintro _ ⟨_, ⟨h,rfl⟩, rfl⟩
  refine ⟨g*h, ?_⟩
  change (InnerProductSpace.rankOne ℂ (π (g*h) x₀) (π (g*h) x₀)).toLinearMap =
    conjugationReal (π g) (InnerProductSpace.rankOne ℂ (π h x₀) (π h x₀)).toLinearMap
  rw [conjugation_rankOne, map_mul]
  rfl

lemma quadraticForm_conj (u : E ≃ₗᵢ[ℂ] E) (T : E →ₗ[ℂ] E) (x : E) :
    quadraticForm (conjugationReal u T) x = quadraticForm T (u.symm x) := by
  unfold quadraticForm
  rw [conjugation_apply]
  have hi := u.inner_map_map (u.symm x) (T (u.symm x))
  rw [u.apply_symm_apply] at hi
  exact congrArg Complex.re hi

/-- A genuine invariant strictly positive frame is obtained by convex averaging;
no Haar measure or compact-group orthogonality is taken as a hypothesis. -/
theorem exists_invariant_frame_of_coercive
    (π : G →* E ≃ₗᵢ[ℂ] E) (x₀ : E)
    (T₀ : E →ₗ[ℂ] E) (hT₀ : T₀ ∈ frameHull π x₀) (hp₀ : T₀.IsPositive)
    (ε : ℝ) (_ : 0 < ε) (hε₀ : T₀ ∈ coerciveSet ε) :
    ∃ T : E →ₗ[ℂ] E, T ∈ frameHull π x₀ ∧ T.IsPositive ∧
      T ∈ coerciveSet ε ∧ ∀ g, conjugationReal (π g) T = T := by
  let K := frameHull π x₀ ∩ ({T | T.IsPositive} ∩ coerciveSet ε)
  have hc : IsClosed K := isClosed_closure.inter (positiveSet_closed.inter (coerciveSet_closed ε))
  have hv : Convex ℝ K := (convex_convexHull ℝ _).closure.inter
    (positiveSet_convex.inter (coerciveSet_convex ε))
  have hL (g : G) (V : E →ₗ[ℂ] E) (hV : V ∈ K) :
      conjugationReal (π g) V ∈ K := by
    refine ⟨frameHull_invariant π x₀ g hV.1, ?_, ?_⟩
    · exact (LinearMap.isPositive_linearIsometryEquiv_conj_iff (π g)).mpr hV.2.1
    · intro x
      rw [quadraticForm_conj]
      simpa only [(π g).symm.norm_map] using hV.2.2 ((π g).symm x)
  obtain ⟨T,hT,hfix⟩ := exists_fixed_minimum K ⟨T₀,hT₀,hp₀,hε₀⟩ hc hv
    (fun g => conjugationReal (π g)) hL
  exact ⟨T,hT.1,hT.2.1,hT.2.2,hfix⟩

end RowColumn.UnitaryFrame
namespace RowColumn.UnitaryFrame
open scoped BigOperators ComplexOrder ComplexConjugate
variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Group G]

omit [FiniteDimensional ℂ E] in
lemma rankOne_quadratic [FiniteDimensional ℂ E] (v x : E) :
    quadraticForm (InnerProductSpace.rankOne ℂ v v).toLinearMap x =
      Complex.normSq (inner ℂ v x) := by
  change (inner ℂ x (inner ℂ v x • v)).re = _
  rw [inner_smul_right, ← inner_conj_symm x v, Complex.mul_conj, Complex.ofReal_re]

omit [FiniteDimensional ℂ E] in
lemma finite_frame_strict [FiniteDimensional ℂ E] (s : Finset E)
    (hs : Submodule.span ℂ (s : Set E) = ⊤)
    {x : E} (hx : x ≠ 0) : 0 < ∑ v ∈ s, Complex.normSq (inner ℂ v x) := by
  have hn : 0 ≤ ∑ v ∈ s, Complex.normSq (inner ℂ v x) :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  by_contra h
  have hz := le_antisymm (le_of_not_gt h) hn
  have hi (v : E) (hv : v ∈ s) : inner ℂ v x = 0 :=
    Complex.normSq_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg
      (fun _ _ => Complex.normSq_nonneg _)).mp hz v hv)
  have hall (v : E) (hv : v ∈ Submodule.span ℂ (s : Set E)) : inner ℂ v x = 0 := by
    induction hv using Submodule.span_induction with
    | mem v hv => exact hi v hv
    | zero => simp
    | add u v hu hv heu hev => simp [heu, hev]
    | smul c v hv hv' => simp [hv']
  exact hx ((inner_self_eq_zero (𝕜 := ℂ)).mp (hall x (by rw [hs]; trivial)))

lemma finiteFrame_quadratic (s : Finset E) (x : E) :
    quadraticForm (finiteFrame s) x = (s.card : ℝ)⁻¹ *
      ∑ v ∈ s, Complex.normSq (inner ℂ v x) := by
  change quadraticEval x (finiteFrame s) = _
  simp only [finiteFrame, Finset.centerMass, one_smul, Finset.sum_const,
    nsmul_eq_mul, mul_one, map_smul, map_sum, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  exact rankOne_quadratic v x

lemma finiteFrame_positive (s : Finset E) (hs : s.Nonempty) : (finiteFrame s).IsPositive := by
  change s.centerMass (fun _ => (1 : ℝ))
    (fun v => (InnerProductSpace.rankOne ℂ v v).toLinearMap) ∈
      {T : E →ₗ[ℂ] E | T.IsPositive}
  apply (positiveSet_convex (E := E)).centerMass_mem (fun _ _ => by norm_num)
  · simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
      (show (0 : ℝ) < s.card from by exact_mod_cast hs.card_pos)
  · intro v _
    exact (InnerProductSpace.isPositive_rankOne_self v).toLinearMap

local instance instNormedAddCommGroupLinearMapComplexId_solutions_1_re57dcf_1 : NormedAddCommGroup (E →ₗ[ℂ] E) := HilbertSchmidt.endCore.toNormedAddCommGroup
/-- Spanning unitary orbits have an invertible positive invariant frame, with
its approximation by finite probability mixtures of the original orbit. -/
theorem exists_invariant_frame (π : G →* E ≃ₗᵢ[ℂ] E) (x₀ : E)
    (hspan : Submodule.span ℂ (Set.range fun g : G => π g x₀) = ⊤) :
    ∃ T : E →ₗ[ℂ] E, T ∈ frameHull π x₀ ∧ T.IsPositive ∧
      Function.Bijective T ∧ ∀ g, conjugationReal (π g) T = T := by
  classical
  obtain ⟨s,hs,hcard,hss,hindep⟩ := Submodule.exists_finset_span_eq_linearIndepOn ℂ
    (Set.range fun g : G => π g x₀)
  let t := insert x₀ s
  have htn : t.Nonempty := Finset.insert_nonempty _ _
  have hts : (t : Set E) ⊆ Set.range fun g : G => π g x₀ := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨1, by simp⟩
    · exact hs hx
  have htspan : Submodule.span ℂ (t : Set E) = ⊤ := by
    apply top_unique
    rw [← hspan, ← hss]
    exact Submodule.span_mono (by intro x hx; exact Finset.mem_insert_of_mem hx)
  have hmem : finiteFrame t ∈ frameHull π x₀ := by
    apply subset_closure
    apply t.centerMass_mem_convexHull (fun _ _ => by norm_num)
    · simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
        (show (0 : ℝ) < t.card from by exact_mod_cast htn.card_pos)
    · intro v hv
      obtain ⟨g,rfl⟩ := hts hv
      exact ⟨g,rfl⟩
  have hstrict (x : E) (hx : x ≠ 0) : 0 < quadraticForm (finiteFrame t) x := by
    rw [finiteFrame_quadratic]
    exact mul_pos (inv_pos.mpr (by exact_mod_cast htn.card_pos)) (finite_frame_strict t htspan hx)
  obtain ⟨ε,hε,hε₀⟩ := positive_coercive (finiteFrame t) hstrict
  obtain ⟨T,hT,hp,hc,hfix⟩ := exists_invariant_frame_of_coercive π x₀ (finiteFrame t)
    hmem (finiteFrame_positive t htn) ε hε hε₀
  have hinj : Function.Injective T := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have hh := hc x
    change ε * ‖x‖^2 ≤ (inner ℂ x (T x)).re at hh
    rw [hx, inner_zero_right, Complex.zero_re] at hh
    have hn : ‖x‖^2 = 0 := le_antisymm (nonpos_of_mul_nonpos_right hh hε) (sq_nonneg _)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  exact ⟨T,hT,hp,⟨hinj, (LinearMap.injective_iff_surjective).mp hinj⟩,hfix⟩

end RowColumn.UnitaryFrame

end
end
end
end


section
noncomputable section
open scoped BigOperators ComplexConjugate ComplexOrder
namespace RowColumn.UnitaryFrame

variable {A G : Type*} [Ring A] [Algebra ℂ A] [StarRing A]
  [FiniteDimensional ℂ A] [Group G]

/-- Algebraic and convex reconstruction from a spanning unitary group. The
trace is the physical trace, not the trace of the algebra's regular action. -/
theorem exists_density (τ : A →ₗ[ℂ] ℂ) (core : InnerProductSpace.Core ℂ A)
    (hinner : ∀ x y, core.inner x y = τ (star x * y))
    (u : G →* unitary A)
    (hspan : Submodule.span ℂ (Set.range fun g : G => (u g : A)) = ⊤) :
    ∃ D : A, τ D = (Module.finrank ℂ A : ℂ) ∧
      (∀ x : A, 0 ≤ τ (star x * x * D)) ∧
      (∀ (B : A) (ℓ : A →ₗ[ℂ] ℂ) (R : ℝ),
        (∀ g, ‖τ (star (u g : A) * (B*D)) * ℓ (u g : A)‖ ≤ R) → ‖ℓ B‖ ≤ R) := by
  let : NormedAddCommGroup A := core.toNormedAddCommGroup
  let : InnerProductSpace ℂ A := InnerProductSpace.ofCore { __ := core }
  change ∀ x y, inner ℂ x y = τ (star x*y) at hinner
  let π : G →* A ≃ₗᵢ[ℂ] A :=
    { toFun := fun g =>
        (Units.mulLeftLinearEquiv ℂ A (Unitary.toUnits (u g))).isometryOfInner (by
          intro x y
          change inner ℂ ((u g : A)*x) ((u g : A)*y) = inner ℂ x y
          simp only [hinner, star_mul, mul_assoc]
          rw [← mul_assoc (star (u g : A)), Unitary.coe_star_mul_self, one_mul])
      map_one' := by ext x; simp
      map_mul' := by intros g h; ext x; simp }
  have hπ (g : G) (x : A) : π g x = (u g : A)*x := rfl
  obtain ⟨T,hT,hpos,hbij,hfix⟩ := exists_invariant_frame π 1 (by simpa only [hπ, mul_one] using hspan)
  have heq (g : G) (x : A) : T ((u g : A)*x) = (u g : A)*T x := by
    have he := LinearMap.congr_fun (hfix g) (π g x)
    change π g (T ((π g).symm (π g x))) = T (π g x) at he
    rw [(π g).symm_apply_apply] at he
    exact he.symm
  let C := T 1
  have hTm (x : A) : T x = x*C := by
    have hx : x ∈ Submodule.span ℂ (Set.range fun g : G => (u g : A)) := by rw [hspan]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨g,rfl⟩ := hx; simpa only [mul_one] using heq g 1
    | zero => simp
    | add x y hx hy hxt hyt => simp only [map_add, add_mul, hxt, hyt]
    | smul c x hx hxt => simpa only [map_smul, smul_mul_assoc] using congrArg (c • ·) hxt
  let e : A ≃ₗ[ℂ] A := LinearEquiv.ofBijective T hbij
  let D : A := e.symm 1
  have hTD : T D = 1 := e.apply_symm_apply 1
  have hDC : D*C = 1 := (hTm D).symm.trans hTD
  have hinv (x : A) : T (x*D) = x := by rw [hTm, mul_assoc, hDC, mul_one]
  have heinv (x : A) : e.symm x = x*D := by
    apply hbij.injective
    exact (e.apply_symm_apply x).trans (hinv x).symm
  have hip : e.symm.toLinearMap.IsPositive := hpos.toLinearMap_symm
  have hDpos (x : A) : 0 ≤ τ (star x*x*D) := by
    have hh := hip.inner_nonneg_right x
    simpa only [LinearEquiv.coe_coe, heinv, hinner, mul_assoc] using hh
  let f : (A →ₗ[ℂ] A) →ₗ[ℂ] ℂ :=
    { toFun S := LinearMap.trace ℂ A (S ∘ₗ LinearMap.mulRight ℂ D)
      map_add' S V := by simp only [LinearMap.add_comp, map_add]
      map_smul' c S := by simp only [LinearMap.smul_comp, map_smul, RingHom.id_apply] }
  have hf (g : G) : f (InnerProductSpace.rankOne ℂ (π g 1) (π g 1)).toLinearMap = τ D := by
    change LinearMap.trace ℂ A (_ ∘ₗ _) = _
    rw [LinearMap.trace_comp_comm']
    have he : LinearMap.mulRight ℂ D ∘ₗ
        (InnerProductSpace.rankOne ℂ (π g 1) (π g 1)).toLinearMap =
        (InnerProductSpace.rankOne ℂ ((π g 1)*D) (π g 1)).toLinearMap := by
      ext x
      simp only [LinearMap.comp_apply, LinearMap.mulRight_apply,
        ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply, smul_mul_assoc]
    rw [he]
    change (InnerProductSpace.rankOne ℂ ((π g 1)*D) (π g 1)).trace ℂ A = _
    rw [InnerProductSpace.trace_rankOne, hinner, hπ, mul_one,
      ← mul_assoc, Unitary.coe_star_mul_self, one_mul]
  let : NormedAddCommGroup (A →ₗ[ℂ] A) := HilbertSchmidt.endCore.toNormedAddCommGroup
  let : InnerProductSpace ℂ (A →ₗ[ℂ] A) :=
    InnerProductSpace.ofCore { __ := HilbertSchmidt.endCore (E := A) }
  let : InnerProductSpace ℝ (A →ₗ[ℂ] A) := InnerProductSpace.complexToReal
  have hfc : ∀ S ∈ frameHull π 1, f S = τ D := by
    change closure (convexHull ℝ _) ⊆ {S | f S = τ D}
    apply closure_minimal
    · apply convexHull_min
      · rintro _ ⟨g,rfl⟩; exact hf g
      · intro S hS V hV a b ha hb hab
        change f (a • S + b • V) = τ D
        rw [map_add, ← Complex.coe_smul a S, ← Complex.coe_smul b V, map_smul, map_smul, hS, hV]
        rw [← add_smul, ← Complex.ofReal_add, hab, Complex.ofReal_one, one_smul]
    · exact isClosed_eq f.toContinuousLinearMap.continuous continuous_const
  have hτD : τ D = (Module.finrank ℂ A : ℂ) := by
    rw [← hfc T hT]
    have hcomp : T ∘ₗ LinearMap.mulRight ℂ D = LinearMap.id := by ext x; exact hinv x
    change LinearMap.trace ℂ A (_ ∘ₗ _) = _
    rw [hcomp, LinearMap.trace_id]
  refine ⟨D,hτD,hDpos,?_⟩
  intro B ℓ R hR
  let l : (A →ₗ[ℂ] A) →ₗ[ℂ] ℂ :=
    { toFun S := ℓ (S (B*D))
      map_add' S V := by simp only [LinearMap.add_apply, map_add]
      map_smul' c S := by simp only [LinearMap.smul_apply, map_smul, RingHom.id_apply] }
  have hl : ∀ S ∈ frameHull π 1, ‖l S‖ ≤ R := by
    change closure (convexHull ℝ _) ⊆ {S | ‖l S‖ ≤ R}
    apply closure_minimal
    · apply convexHull_min
      · rintro _ ⟨g,rfl⟩
        change ‖ℓ ((InnerProductSpace.rankOne ℂ (π g 1) (π g 1)) (B*D))‖ ≤ R
        simpa only [l, LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.coe_coe,
          InnerProductSpace.rankOne_apply, map_smul, hinner, hπ, mul_one, smul_eq_mul] using hR g
      · intro S hS V hV a b ha hb hab
        change ‖l (a • S + b • V)‖ ≤ R
        rw [map_add, ← Complex.coe_smul a S, ← Complex.coe_smul b V, map_smul, map_smul]
        calc
          _ ≤ ‖(a : ℂ) • l S‖ + ‖(b : ℂ) • l V‖ := norm_add_le _ _
          _ = a * ‖l S‖ + b * ‖l V‖ := by simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
          _ ≤ a*R+b*R := add_le_add (mul_le_mul_of_nonneg_left hS ha) (mul_le_mul_of_nonneg_left hV hb)
          _ = R := by rw [← add_mul, hab, one_mul]
    · exact isClosed_le l.toContinuousLinearMap.continuous.norm continuous_const
  simpa only [l, LinearMap.coe_mk, AddHom.coe_mk, hinv] using hl T hT

end RowColumn.UnitaryFrame

end
end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.FiniteUnitary_Reconstruction
attribute [-instance] _root_.OAI.RowColumn.MatrixState.matrixAlgebraIsClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators ComplexOrder
namespace RowColumn.UnitaryFrame
variable {A G : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [FiniteDimensional ℂ A] [Group G]

omit [FiniteDimensional ℂ A] in
lemma positive_functional_bound (f : A →ₚ[ℂ] ℂ) (x : A) :
    ‖f x‖ ≤ 4 * ‖f 1‖ * ‖x‖ := by
  obtain ⟨y, hy_nonneg, hy_norm, hy⟩ := CStarAlgebra.exists_sum_four_nonneg x
  conv_lhs => rw [hy]
  simp only [map_sum, map_smul]
  apply (norm_sum_le _ _).trans
  simp only [norm_smul, norm_pow, Complex.norm_I, one_pow, one_mul]
  apply (Finset.sum_le_sum (g := fun _ => ‖f 1‖ * ‖x‖) (fun i _ => ?_)).trans
  · simp [mul_assoc]
  · exact (f.norm_apply_le_of_nonneg _ (hy_nonneg i)).trans
      (mul_le_mul_of_nonneg_left (hy_norm i) (norm_nonneg _))

/-- Finite-dimensional unitary reconstruction with polynomial Fourier cost.
Only the actual operator norm of B occurs; the auxiliary Hilbert norm is used
solely to construct the frame and does not alter that norm. -/
theorem reconstruction_bound (τ : A →ₗ[ℂ] ℂ) (core : InnerProductSpace.Core ℂ A)
    (hinner : ∀ x y, core.inner x y = τ (star x*y))
    (u : G →* unitary A)
    (hspan : Submodule.span ℂ (Set.range fun g : G => (u g : A)) = ⊤)
    (B : A) (ℓ : A →ₗ[ℂ] ℂ) (R : ℝ) (_ : 0 ≤ R)
    (hU : ∀ g, ‖ℓ (u g : A)‖ ≤ R) :
    ‖ℓ B‖ ≤ 4 * (Module.finrank ℂ A : ℝ) * ‖B‖ * R := by
  obtain ⟨D,hD,hpos,hrec⟩ := exists_density τ core hinner u hspan
  let φ : A →ₗ[ℂ] ℂ := τ.comp (LinearMap.mulRight ℂ D)
  have hφpos (a : A) (ha : 0 ≤ a) : 0 ≤ φ a := by
    have hh := hpos (CFC.sqrt a)
    have hs : star (CFC.sqrt a) * CFC.sqrt a = a := by
      rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)).star_eq]
      exact CFC.sqrt_mul_sqrt_self a ha
    change 0 ≤ τ (a*D)
    simpa only [hs] using hh
  let f : A →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ φ hφpos
  have hf1 : ‖f 1‖ = (Module.finrank ℂ A : ℝ) := by
    change ‖τ (1*D)‖ = _
    rw [one_mul, hD]
    simp
  apply hrec B ℓ
  intro g
  rw [← mul_assoc]
  change ‖φ (star (u g : A)*B) * ℓ (u g : A)‖ ≤ _
  rw [norm_mul]
  have hb : ‖φ (star (u g : A)*B)‖ ≤ 4 * (Module.finrank ℂ A : ℝ) * ‖B‖ := by
    have hh := positive_functional_bound f (star (u g : A)*B)
    rw [hf1] at hh
    change ‖f (star (u g : A)*B)‖ ≤ _
    simpa only [← Unitary.coe_star, CStarRing.norm_coe_unitary_mul] using hh
  exact mul_le_mul hb (hU g) (norm_nonneg _) (by positivity)

end RowColumn.UnitaryFrame
noncomputable section
open scoped ComplexConjugate

namespace RowColumn.FiniteStarAlgebra
open scoped ComplexOrder
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

lemma core_inner_trace (A : StarSubalgebra ℂ (Ambient (E := E))) (a b : A) :
    (algebraCore A).inner a b = physicalTrace A (star a*b) := by
  change LinearMap.trace ℂ E (LinearMap.adjoint (a : Ambient (E := E)).toLinearMap ∘ₗ
    (b : Ambient (E := E)).toLinearMap) = LinearMap.trace ℂ E ((star (a : Ambient (E := E)) * (b : Ambient (E := E))).toLinearMap)
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_toLinearMap]
  rfl

end RowColumn.FiniteStarAlgebra
end
end
end


section
noncomputable section
open scoped ComplexOrder
noncomputable section
open scoped BigOperators ComplexOrder
namespace RowColumn.UnitaryFrame
variable {A G E : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [FiniteDimensional ℂ A] [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The finite Fourier reconstruction bound for arbitrary Hilbert-valued
linear maps, in particular weighted Hilbert–Schmidt sandwich maps. -/
theorem reconstruction_hilbert_bound (τ : A →ₗ[ℂ] ℂ) (core : InnerProductSpace.Core ℂ A)
    (hinner : ∀ x y, core.inner x y = τ (star x*y))
    (u : G →* unitary A)
    (hspan : Submodule.span ℂ (Set.range fun g : G => (u g : A)) = ⊤)
    (B : A) (F : A →ₗ[ℂ] E) (R : ℝ) (hR : 0 ≤ R)
    (hU : ∀ g, ‖F (u g : A)‖ ≤ R) :
    ‖F B‖ ≤ 4 * (Module.finrank ℂ A : ℝ) * ‖B‖ * R := by
  let ℓ := (innerSL ℂ (F B)).toLinearMap.comp F
  have hu (g : G) : ‖ℓ (u g : A)‖ ≤ ‖F B‖ * R :=
    (norm_inner_le_norm (F B) (F (u g : A))).trans
      (mul_le_mul_of_nonneg_left (hU g) (norm_nonneg _))
  have hh := reconstruction_bound τ core hinner u hspan B ℓ (‖F B‖ * R)
    (mul_nonneg (norm_nonneg _) hR) hu
  change ‖inner ℂ (F B) (F B)‖ ≤ _ at hh
  rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg _)] at hh
  by_cases hz : ‖F B‖=0
  · rw [hz]
    positivity
  · have hp : 0 < ‖F B‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith [hh]

end RowColumn.UnitaryFrame
noncomputable section
namespace RowColumn
variable {A : Type*} [CStarAlgebra A]

lemma supported_fourth (q F : A) (hq : q*q=q) (hc : Commute q F) :
    (q*F)^4 = q*(F^4) := by
  rw [hc.mul_pow]
  have hq4 : q^4=q := by calc
    q^4=(q*q)*(q*q) := by noncomm_ring
    _=q := by rw [hq,hq]
  rw [hq4]

/-- The quarter-root estimate at the level of the genuine operator norm.
The two fourth-moment bounds imply the exact squared sandwich bound. -/
theorem filterNorm_sq (q F G : A) (hsq : IsSelfAdjoint q) (hqq : q*q=q)
    (hF : IsSelfAdjoint F) (hG : IsSelfAdjoint G) (hcF : Commute q F) (hcG : Commute q G)
    (d : ℝ) (_ : 0 < d) (hFb : ‖q * F^4‖ ≤ 1/d) (hGb : ‖q * G^4‖ ≤ 1/d) :
    ‖F*q*G‖^2 ≤ 1/d := by
  have hsF : IsSelfAdjoint (q*F) := by
    change star (q*F)=q*F
    rw [star_mul,hsq.star_eq,hF.star_eq,hcF.eq]
  have hsG : IsSelfAdjoint (q*G) := by
    change star (q*G)=q*G
    rw [star_mul,hsq.star_eq,hG.star_eq,hcG.eq]
  have hnF : ‖q*F‖^4 ≤ 1/d := by
    have hn : ‖(q*F)^4‖=‖q*F‖^4 := by simpa using hsF.norm_pow_two_pow 2
    rw [← hn,supported_fourth q F hqq hcF]
    exact hFb
  have hnG : ‖q*G‖^4 ≤ 1/d := by
    have hn : ‖(q*G)^4‖=‖q*G‖^4 := by simpa using hsG.norm_pow_two_pow 2
    rw [← hn,supported_fourth q G hqq hcG]
    exact hGb
  have he : F*q*G=(q*F)*(q*G) := by
    calc
      _ = F*(q*q)*G := by rw [hqq]
      _ = (F*q)*(q*G) := by noncomm_ring
      _ = _ := by rw [hcF.eq]
  have hn := norm_mul_le (q*F) (q*G)
  rw [← he] at hn
  have hp : (‖q*F‖*‖q*G‖)^2 ≤ 1/d := by
    have ha := sq_nonneg (‖q*F‖^2-‖q*G‖^2)
    nlinarith
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hp
end RowColumn

end
end
end
end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.MatrixState_HilbertSchmidt
attribute [-instance] _root_.OAI.RowColumn.FiniteStarAlgebra.algebraFiniteDimensional _root_.OAI.RowColumn.FiniteStarAlgebra.algebraIsClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
variable {I J : Type*} [Fintype I] [Fintype J]

lemma hsVector_inner (M N : Matrix I J ℂ) :
    inner ℂ (hsVector M) (hsVector N) = (M.conjTranspose*N).trace := by
  change (∑ z : I × J, N z.1 z.2 * star (M z.1 z.2)) = _
  rw [Fintype.sum_prod_type]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  simp only [mul_comm]

lemma hsVector_norm_sq (M : Matrix I J ℂ) :
    ‖hsVector M‖^2 = (M.conjTranspose*M).trace.re := by
  rw [← hsVector_inner M M, inner_self_eq_norm_sq_to_K]
  simp only [← Complex.ofReal_pow, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re]

lemma trace_mH_mul_le (M N : Matrix I J ℂ) :
    (M.conjTranspose*N).trace.re ≤ Real.sqrt ((M.conjTranspose*M).trace.re) *
      Real.sqrt ((N.conjTranspose*N).trace.re) := by
  rw [← hsVector_inner M N, ← hsVector_norm_sq M, ← hsVector_norm_sq N,
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  exact (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)

variable [DecidableEq I]

lemma trace_mul_psd_nonneg (A B : Matrix I I ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A*B).trace.re := by
  let R : Matrix I I ℂ := CFC.sqrt B
  have hs : R.conjTranspose=R := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)).isHermitian.eq
  have hsq : R*R=B := CFC.sqrt_mul_sqrt_self B hB.nonneg
  have hh := (hA.conjTranspose_mul_mul_same R).trace_nonneg
  rw [hs] at hh
  have ht : (R*A*R).trace=(A*B).trace := by
    rw [Matrix.trace_mul_cycle,hsq,Matrix.trace_mul_comm]
  rw [ht] at hh
  exact hh.1

lemma trace_sqrt_conjugate_le_one (A B U : Matrix I I ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hTA : A.trace.re ≤ 1) (hTB : B.trace.re ≤ 1) (hU : U ∈ unitary (Matrix I I ℂ)) :
    (CFC.sqrt A * U * CFC.sqrt B * U.conjTranspose).trace.re ≤ 1 := by
  let X : Matrix I I ℂ := CFC.sqrt A
  let Y : Matrix I I ℂ := U * CFC.sqrt B * U.conjTranspose
  have hx : X.conjTranspose=X := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.eq
  have hy : Y.conjTranspose=Y := by simp [Y,Matrix.conjTranspose_mul,
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)).isHermitian.eq, mul_assoc]
  have hy2 : Y*Y=U*B*U.conjTranspose := by
    have hu : U.conjTranspose*U=1 := hU.1
    dsimp only [Y]
    calc
      _=U*CFC.sqrt B*(U.conjTranspose*U)*CFC.sqrt B*U.conjTranspose := by noncomm_ring
      _=U*B*U.conjTranspose := by rw [hu,mul_one]; rw [mul_assoc U, CFC.sqrt_mul_sqrt_self B hB.nonneg]
  have hx2 : X*X=A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  have ht : (Y*Y).trace=B.trace := by
    rw [hy2,Matrix.trace_mul_cycle]
    have hu : U.conjTranspose*U=1 := hU.1
    rw [hu,one_mul]
  have hc := trace_mH_mul_le X Y
  rw [hx,hy,hx2,ht] at hc
  have hsA : Real.sqrt A.trace.re ≤ 1 := (Real.sqrt_le_one).mpr hTA
  have hsB : Real.sqrt B.trace.re ≤ 1 := (Real.sqrt_le_one).mpr hTB
  have hprod := mul_le_mul hsA hsB (Real.sqrt_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  have hh := hc.trans hprod
  simpa only [X,Y,← mul_assoc,one_mul] using hh
end RowColumn.MatrixState

end
end

section

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]

lemma toEuclideanCLM_positive_iff (A : Matrix I I ℂ) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) A).IsPositive ↔ A.PosSemidef := by
  rw [← ContinuousLinearMap.isPositive_toLinearMap_iff]
  exact Matrix.isPositive_toEuclideanLin_iff

lemma trace_toEuclideanCLM (A : Matrix I I ℂ) :
    LinearMap.trace ℂ (EuclideanSpace ℂ I)
      (Matrix.toEuclideanCLM (𝕜 := ℂ) A).toLinearMap = A.trace := by
  exact Matrix.trace_toLin_eq A (EuclideanSpace.basisFun I ℂ).toBasis

omit [DecidableEq I] [DecidableEq J] in
lemma hsVector_norm_sq_sum (M : Matrix I J ℂ) :
    ‖hsVector M‖^2 = ∑ i, ∑ j, ‖M i j‖^2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  rfl

lemma finite_sum_embedding_le {D E : Type*} [Fintype D] [Fintype E]
    (e : D ↪ E) (f : E → ℝ) (hf : ∀ i, 0 ≤ f i) : ∑ i, f (e i) ≤ ∑ i, f i := by
  rw [← Finset.sum_image (fun i _ j _ h => e.injective h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _ => hf i)

omit [DecidableEq I] [DecidableEq J] in
lemma hsVector_submatrix_norm_sq_le {I' J' : Type*} [Fintype I'] [Fintype J']
    [DecidableEq I'] [DecidableEq J'] (e : I' ↪ I) (f : J' ↪ J) (M : Matrix I J ℂ) :
    ‖hsVector (M.submatrix e f)‖^2 ≤ ‖hsVector M‖^2 := by
  rw [hsVector_norm_sq_sum, hsVector_norm_sq_sum]
  calc
    _ ≤ ∑ i : I', ∑ j : J, ‖M (e i) j‖^2 := Finset.sum_le_sum fun i _ =>
      finite_sum_embedding_le f (fun j => ‖M (e i) j‖^2) (fun _ => sq_nonneg _)
    _ ≤ _ := finite_sum_embedding_le e (fun i => ∑ j, ‖M i j‖^2)
      (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- The exact Hilbert--Schmidt trace formula used in the two PSD majorizations. -/
lemma hsVector_sandwich_sq (A B X : Matrix I I ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ‖hsVector (A * X * B)‖^2 = (A^2 * X * B^2 * X.conjTranspose).trace.re := by
  rw [hsVector_norm_sq]
  simp only [Matrix.conjTranspose_mul, hA.eq, hB.eq]
  congr 1
  calc
    _ = ((B * X.conjTranspose) * (A*A*X*B)).trace := by
      simp only [mul_assoc]
    _ = ((A*A*X*B) * (B * X.conjTranspose)).trace := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [pow_two, mul_assoc]

end RowColumn.MatrixState

end
end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.MatrixState_QuarterRoot
attribute [-instance] _root_.OAI.RowColumn.FiniteStarAlgebra.algebraFiniteDimensional _root_.OAI.RowColumn.FiniteStarAlgebra.algebraIsClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
variable {C : Type*} [Fintype C] [DecidableEq C]

lemma quarter_square (A : Matrix C C ℂ) : quarterRoot A * quarterRoot A = CFC.sqrt A :=
  CFC.sqrt_mul_sqrt_self _ (CFC.sqrt_nonneg _)
lemma quarter_four (A : Matrix C C ℂ) (hA : A.PosSemidef) : quarterRoot A ^ 4 = A := by
  calc
    _ = (quarterRoot A * quarterRoot A) * (quarterRoot A * quarterRoot A) := by noncomm_ring
    _ = A := by rw [quarter_square, CFC.sqrt_mul_sqrt_self A hA.nonneg]

lemma inverseQuarter_positive (A : Matrix C C ℂ) : (inverseQuarter A).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  apply cfc_nonneg
  intro x hx
  apply inv_nonneg.mpr
  exact spectrum_nonneg_of_nonneg (CFC.sqrt_nonneg _) hx

lemma inverseQuarter_commute (A : Matrix C C ℂ) : Commute (inverseQuarter A) (quarterRoot A) := by
  exact (Commute.refl _).cfc (by rw [Matrix.star_eq_conjTranspose, (quarter_positive A).isHermitian.eq]; exact Commute.refl _) _

lemma quarter_inverse_quarter (A : Matrix C C ℂ) :
    quarterRoot A * inverseQuarter A * quarterRoot A = quarterRoot A := by
  let Q := quarterRoot A
  have hQ : IsSelfAdjoint Q := (quarter_positive A).isHermitian
  have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ Q) := by
    rw [continuousOn_iff_continuous_domRestrict]
    fun_prop
  change Q * cfc (fun x : ℝ => x⁻¹) Q * Q = Q
  calc
    _ = cfc (fun x : ℝ => x * x⁻¹ * x) Q := by
      rw [cfc_mul _ _ Q (hc _) (hc _), cfc_mul _ _ Q (hc _) (hc _), cfc_id' ℝ Q hQ]
    _ = Q := by
      rw [show (fun x : ℝ => x*x⁻¹*x) = (fun x => x) by funext x; simp, cfc_id' ℝ Q hQ]

lemma quarterSupport_hermitian (A : Matrix C C ℂ) : (quarterSupport A).IsHermitian := by
  change star (quarterRoot A * inverseQuarter A) = _
  rw [star_mul, Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose, (quarter_positive A).isHermitian.eq, (inverseQuarter_positive A).isHermitian.eq]
  exact inverseQuarter_commute A

lemma quarterSupport_mul (A : Matrix C C ℂ) (hA : A.PosSemidef) : quarterSupport A * A = A := by
  conv_lhs => rhs; rw [← quarter_four A hA]
  conv_rhs => rw [← quarter_four A hA]
  change (quarterRoot A * inverseQuarter A) * quarterRoot A ^ 4 = quarterRoot A ^ 4
  calc
    _ = (quarterRoot A * inverseQuarter A * quarterRoot A) * quarterRoot A ^ 3 := by noncomm_ring
    _ = _ := by rw [quarter_inverse_quarter]; noncomm_ring

lemma quarter_whitening_mean (A : Matrix C C ℂ) (hA : A.PosSemidef) :
    inverseQuarter A * A * inverseQuarter A = quarterRoot A * quarterRoot A := by
  conv_lhs => lhs; rhs; rw [← quarter_four A hA]
  have hc := inverseQuarter_commute A
  calc
    _ = (inverseQuarter A * quarterRoot A) * quarterRoot A * quarterRoot A *
      (quarterRoot A * inverseQuarter A) := by noncomm_ring
    _ = (quarterRoot A * inverseQuarter A) * quarterRoot A * quarterRoot A *
      (quarterRoot A * inverseQuarter A) := by rw [hc.eq]
    _ = (quarterRoot A * inverseQuarter A) * quarterRoot A * quarterRoot A *
      (inverseQuarter A * quarterRoot A) := by conv_lhs => rhs; rw [← hc.eq]
    _ = (quarterRoot A * inverseQuarter A * quarterRoot A) *
      (quarterRoot A * inverseQuarter A * quarterRoot A) := by noncomm_ring
    _ = _ := by rw [quarter_inverse_quarter]

/-- Kernel propagation for positive matrices, used to justify all inverses on
supports in the quarter-root normalization, including singular states. -/
lemma positive_kernel_mono (S A P : Matrix C C ℂ) (hS : S.PosSemidef)
    (hle : S ≤ A) (hP : P.IsHermitian) (hPA : P*A=0) : P*S=0 := by
  have hcong : P*S*P ≤ P*A*P := by
    have hh := (show (A-S).PosSemidef from hle).conjTranspose_mul_mul_same P
    change (P*A*P-P*S*P).PosSemidef
    simpa only [hP.eq, Matrix.mul_sub, Matrix.sub_mul] using hh
  have hp : 0 ≤ P*S*P := by
    simpa only [hP.eq] using (hS.conjTranspose_mul_mul_same P).nonneg
  rw [hPA, zero_mul] at hcong
  have hz : P*S*P=0 := le_antisymm hcong hp
  let R : Matrix C C ℂ := CFC.sqrt S
  have hs : star R=R := (CFC.sqrt_nonneg S).isSelfAdjoint
  have hsq : R*R=S := CFC.sqrt_mul_sqrt_self S hS.nonneg
  have hr : R*P=0 := by
    apply (CStarRing.star_mul_self_eq_zero_iff _).mp
    rw [star_mul, hs, Matrix.star_eq_conjTranspose, hP.eq, ← mul_assoc, mul_assoc P R R, hsq, hz]
  have hl : P*R=0 := by simpa only [star_mul, hs, Matrix.star_eq_conjTranspose, hP.eq, star_zero] using congrArg star hr
  rw [← hsq, ← mul_assoc, hl, zero_mul]

lemma quarterSupport_of_le (A S : Matrix C C ℂ) (hA : A.PosSemidef)
    (hS : S.PosSemidef) (hle : S ≤ A) : quarterSupport A * S = S := by
  have hP : (1-quarterSupport A).IsHermitian := (Matrix.isHermitian_one).sub (quarterSupport_hermitian A)
  have hz : (1-quarterSupport A)*A=0 := by rw [sub_mul, one_mul, quarterSupport_mul A hA, sub_self]
  have hh := positive_kernel_mono S A (1-quarterSupport A) hS hle hP hz
  rw [sub_mul, one_mul] at hh
  exact (sub_eq_zero.mp hh).symm

lemma undo_quarter_whitening (A S : Matrix C C ℂ) (hS : S.IsHermitian)
    (hsupp : quarterSupport A * S=S) :
    quarterRoot A * (inverseQuarter A * S * inverseQuarter A) * quarterRoot A = S := by
  have hsupp' : S*quarterSupport A=S := by
    simpa only [star_mul, Matrix.star_eq_conjTranspose, hS.eq, (quarterSupport_hermitian A).eq] using congrArg star hsupp
  calc
    _ = quarterSupport A * S * quarterSupport A := by
      have hc := (inverseQuarter_commute A).eq
      dsimp only [quarterSupport]
      noncomm_ring [hc]
    _ = S := by rw [hsupp,hsupp']

end RowColumn.MatrixState

end
end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.MatrixState_Postselection
attribute [-instance] _root_.OAI.RowColumn.FiniteStarAlgebra.algebraFiniteDimensional _root_.OAI.RowColumn.FiniteStarAlgebra.algebraIsClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Classical Nat


noncomputable section
open scoped BigOperators Classical

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]

omit [DecidableEq C] in
lemma tensorMatrix_trace (A : S → Matrix C C ℂ) :
    (tensorMatrix A).trace = ∏ i, (A i).trace := by
  simp only [tensorMatrix, Matrix.trace, Matrix.diag]
  exact (Fintype.prod_sum (fun i : S => fun c : C => A i c c)).symm

lemma tensorMatrix_posSemidef (A : S → Matrix C C ℂ) (hA : ∀ i, (A i).PosSemidef) :
    (tensorMatrix A).PosSemidef := by
  let B := fun i => CFC.sqrt (A i)
  have hb (i : S) : (B i).conjTranspose * B i = A i := by
    rw [(Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (A i))).isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self _ (hA i).nonneg
  have he : (tensorMatrix B).conjTranspose * tensorMatrix B = tensorMatrix A := by
    rw [tensorMatrix_star, tensorMatrix_mul]
    simp_rw [hb]
  rw [← he]
  exact Matrix.posSemidef_conjTranspose_mul_self _

end RowColumn.MatrixState

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.RowColumn_Sectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Classical Matrix.Norms.L2Operator MatrixOrder

noncomputable section

noncomputable section
namespace RowColumn.FiniteStarAlgebra
variable {R A G : Type*} [CommSemiring R] [StarRing R] [Ring A] [Algebra R A]
  [StarRing A] [StarModule R A] [Group G]

lemma unitarySpan_eq_span (u : G →* unitary A) :
    (unitarySpan (R := R) u).toSubmodule = Submodule.span R (Set.range fun g : G => (u g : A)) := by
  apply Algebra.adjoin_eq_span_of_subset
  intro a ha
  have hh : a ∈ Set.range (fun g : G => (u g : A)) := by
    induction ha using Submonoid.closure_induction with
    | mem a ha => exact ha
    | one => exact ⟨1,by simp⟩
    | mul a b ha hb iha ihb =>
      obtain ⟨g,rfl⟩ := iha
      obtain ⟨h,rfl⟩ := ihb
      exact ⟨g*h,by simp⟩
  exact Submodule.subset_span hh

lemma unitarySpanHom_spans (u : G →* unitary A) :
    Submodule.span R (Set.range fun g : G => (unitarySpanHom (R := R) u g : unitarySpan (R := R) u))=⊤ := by
  apply Submodule.map_injective_of_injective (Submodule.subtype_injective (unitarySpan (R := R) u).toSubmodule)
  rw [Submodule.map_span, ← Set.range_comp]
  change Submodule.span R (Set.range fun g : G => (u g : A)) =
    Submodule.map (unitarySpan (R := R) u).toSubmodule.subtype ⊤
  rw [Submodule.map_top, Submodule.range_subtype]
  exact (unitarySpan_eq_span u).symm

end RowColumn.FiniteStarAlgebra

end
end
end
end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.MatrixState_Whitening
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
variable {C L : Type*} [Fintype C] [DecidableEq C] [Fintype L]

omit [Fintype C] [DecidableEq C] in
lemma stateMean_positive (p : L → ℝ) (S : L → Matrix C C ℂ)
    (hp : ∀ i, 0 ≤ p i) (hS : ∀ i, (S i).PosSemidef) : (stateMean p S).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  exact Finset.sum_nonneg fun i _ => ((hS i).smul (hp i)).nonneg

omit [Fintype C] [DecidableEq C] in
lemma smul_le_stateMean (p : L → ℝ) (S : L → Matrix C C ℂ)
    (hp : ∀ i, 0 ≤ p i) (hS : ∀ i, (S i).PosSemidef) (i : L) : p i • S i ≤ stateMean p S := by
  exact Finset.single_le_sum (fun j _ => ((hS j).smul (hp j)).nonneg) (Finset.mem_univ i)

omit [DecidableEq C] in
lemma stateMean_trace_le_one (p : L → ℝ) (S : L → Matrix C C ℂ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i=1) (hS : ∀ i, (S i).trace.re ≤ 1) :
    (stateMean p S).trace.re ≤ 1 := by
  change (Matrix.trace (∑ i, p i • S i)).re ≤ 1
  rw [Matrix.trace_sum, Complex.re_sum]
  calc
    _ = ∑ i, p i * (S i).trace.re := by simp
    _ ≤ ∑ i, p i := Finset.sum_le_sum fun i _ => by nlinarith [hS i,hp i]
    _ = 1 := hpsum

lemma mean_support (p : L → ℝ) (S : L → Matrix C C ℂ)
    (hp : ∀ i, 0 ≤ p i) (hS : ∀ i, (S i).PosSemidef) (i : L) (hi : 0 < p i) :
    quarterSupport (stateMean p S) * S i = S i := by
  have hh := quarterSupport_of_le (stateMean p S) (p i • S i)
    (stateMean_positive p S hp hS) ((hS i).smul (hp i)) (smul_le_stateMean p S hp hS i)
  rw [mul_smul_comm] at hh
  exact (smul_right_injective _ (ne_of_gt hi)) hh

lemma whitenState_positive (A S : Matrix C C ℂ) (hS : S.PosSemidef) :
    (whitenState A S).PosSemidef := by
  simpa only [whitenState, (inverseQuarter_positive A).isHermitian.eq] using
    hS.conjTranspose_mul_mul_same (inverseQuarter A)

lemma stateMean_whiten (p : L → ℝ) (S : L → Matrix C C ℂ)
    (hp : ∀ i, 0 ≤ p i) (hS : ∀ i, (S i).PosSemidef) :
    stateMean p (fun i => whitenState (stateMean p S) (S i)) = CFC.sqrt (stateMean p S) := by
  change (∑ i, p i • (inverseQuarter (stateMean p S) * S i * inverseQuarter (stateMean p S))) = _
  rw [show (∑ i, p i • (inverseQuarter (stateMean p S) * S i * inverseQuarter (stateMean p S))) =
    inverseQuarter (stateMean p S) * stateMean p S * inverseQuarter (stateMean p S) by
      simp [stateMean, Finset.mul_sum, Finset.sum_mul]]
  rw [quarter_whitening_mean _ (stateMean_positive p S hp hS), quarter_square]

lemma unwhitenState (p : L → ℝ) (S : L → Matrix C C ℂ)
    (hp : ∀ i, 0 ≤ p i) (hS : ∀ i, (S i).PosSemidef) (i : L) (hi : 0 < p i) :
    quarterRoot (stateMean p S) * whitenState (stateMean p S) (S i) * quarterRoot (stateMean p S) = S i :=
  undo_quarter_whitening _ _ (hS i).isHermitian (mean_support p S hp hS i hi)

lemma stateMean_even (odd : C → Prop) (p : L → ℝ) (S : L → Matrix C C ℂ)
    (hS : ∀ i, S i ∈ evenAlgebra odd) : stateMean p S ∈ evenAlgebra odd := by
  apply (evenAlgebra odd).sum_mem
  intro i _ c d h
  change p i • S i c d=0
  rw [hS i c d h, smul_zero]

lemma inverseQuarter_even (odd : C → Prop) (A : Matrix C C ℂ) (hA : A.PosSemidef)
    (he : A ∈ evenAlgebra odd) : inverseQuarter A ∈ evenAlgebra odd := by
  let : IsClosed ((evenAlgebra odd) : Set (Matrix C C ℂ)) :=
    (evenAlgebra odd).toSubalgebra.toSubmodule.closed_of_finiteDimensional
  exact cfc_mem (𝕜 := ℝ) (𝕜' := ℂ) (s := evenAlgebra odd) (fun x : ℝ => x⁻¹) (quarter_even odd A hA he)

lemma whitenState_even (odd : C → Prop) (A S : Matrix C C ℂ) (hA : A.PosSemidef)
    (heA : A ∈ evenAlgebra odd) (heS : S ∈ evenAlgebra odd) : whitenState A S ∈ evenAlgebra odd := by
  exact (evenAlgebra odd).mul_mem
    ((evenAlgebra odd).mul_mem (inverseQuarter_even odd A hA heA) heS)
    (inverseQuarter_even odd A hA heA)
end RowColumn.MatrixState

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
variable {C L K : Type*} [Fintype C] [DecidableEq C] [Fintype L] [Fintype K]

/-- The independent marginal mean of the local squared Hilbert--Schmidt factors,
with no invertibility assumption on either average state. -/
lemma independent_overlap_mean (p : L → ℝ) (q : K → ℝ)
    (S : L → Matrix C C ℂ) (T : K → Matrix C C ℂ) (U : Matrix C C ℂ) :
    (∑ i, ∑ j, p i * q j * (S i * U * T j * U.conjTranspose).trace.re) =
      (stateMean p S * U * stateMean q T * U.conjTranspose).trace.re := by
  simp only [stateMean, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum]
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, mul_assoc]
  simp only [Complex.re_sum, Finset.mul_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Quarter-root whitening makes the independent mean at most one, while
preserving singular substates exactly on every occupied fibre. -/
theorem weighted_whitened_mean_le_one (p : L → ℝ) (q : K → ℝ)
    (S : L → Matrix C C ℂ) (T : K → Matrix C C ℂ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j)
    (hpsum : ∑ i, p i = 1) (hqsum : ∑ j, q j = 1)
    (hS : ∀ i, (S i).PosSemidef) (hT : ∀ j, (T j).PosSemidef)
    (hStr : ∀ i, (S i).trace.re ≤ 1) (hTtr : ∀ j, (T j).trace.re ≤ 1)
    (U : Matrix C C ℂ) (hU : U ∈ unitary (Matrix C C ℂ)) :
    (∑ i, ∑ j, p i * q j *
      (whitenState (stateMean p S) (S i) * U *
        whitenState (stateMean q T) (T j) * U.conjTranspose).trace.re) ≤ 1 := by
  rw [independent_overlap_mean, stateMean_whiten p S hp hS, stateMean_whiten q T hq hT]
  exact trace_sqrt_conjugate_le_one _ _ U (stateMean_positive p S hp hS)
    (stateMean_positive q T hq hT) (stateMean_trace_le_one p S hp hpsum hStr)
    (stateMean_trace_le_one q T hq hqsum hTtr) hU

lemma local_overlap_nonneg (A B U : Matrix C C ℂ) (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ (A * U * B * U.conjTranspose).trace.re := by
  simpa only [mul_assoc] using trace_mul_psd_nonneg A (U * B * U.conjTranspose)
    hA (hB.mul_mul_conjTranspose_same U)

end RowColumn.MatrixState

end
end
end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.RowColumn_Entropy
attribute [-instance] _root_.OAI.RowColumn.FiniteStarAlgebra.algebraFiniteDimensional _root_.OAI.RowColumn.FiniteStarAlgebra.algebraIsClosed _root_.OAI.RowColumn.MatrixState.matrixAlgebraIsClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Classical
namespace RowColumn

/-- Entropy of a distribution on k symbols is at most log k, including
zero probabilities. This is the marginal-entropy step in both grid proofs. -/
lemma entropy_le_log_card {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    -∑ i, p i * Real.log (p i) ≤ Real.log (Fintype.card ι) := by
  have hk : 0 < Fintype.card ι := by
    by_contra h
    have he : IsEmpty ι := Fintype.card_eq_zero_iff.mp (by omega)
    have := hs
    simp at this
  have hkR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hk
  have hb : ∀ i, -p i * Real.log (p i) - p i * Real.log (Fintype.card ι) ≤
      1 / Fintype.card ι - p i := by
    intro i
    by_cases hpi : p i = 0
    · simp [hpi]
    · have hpi' : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm hpi)
      have hl := mul_le_mul_of_nonneg_left
        (Real.log_le_sub_one_of_pos (one_div_pos.mpr (mul_pos hkR hpi'))) (hp i)
      rw [Real.log_div (by norm_num) (mul_ne_zero (ne_of_gt hkR) hpi),
        Real.log_one, Real.log_mul (ne_of_gt hkR) hpi] at hl
      have he : p i * (1 / ((Fintype.card ι : ℝ) * p i) - 1) =
          1 / Fintype.card ι - p i := by field_simp
      rw [he] at hl
      nlinarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hb i)
  simp only [neg_mul, Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_neg_distrib,
    hs, one_mul] at hsum
  have hc : ∑ _i : ι, 1 / (Fintype.card ι : ℝ) = 1 := by
    simp [div_eq_mul_inv, ne_of_gt hkR]
  rw [hc] at hsum
  linarith


lemma uniformMarginal_nonneg {ι α : Type*} [Fintype ι] [DecidableEq α]
    (f : ι → α) (a : α) : 0 ≤ uniformMarginal f a := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> positivity

lemma sum_uniformMarginal_mul {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    (f : ι → α) (g : α → ℝ) :
    ∑ a, uniformMarginal f a * g a = (Fintype.card ι : ℝ)⁻¹ * ∑ i, g (f i) := by
  simp only [uniformMarginal, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [ite_mul, zero_mul]
  simp [← Finset.mul_sum]

lemma sum_uniformMarginal {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    [Nonempty ι] (f : ι → α) : ∑ a, uniformMarginal f a = 1 := by
  simpa using sum_uniformMarginal_mul f (fun _ => 1)

lemma uniformMarginal_pos {ι α : Type*} [Fintype ι] [DecidableEq α]
    [Nonempty ι] (f : ι → α) (i : ι) : 0 < uniformMarginal f (f i) := by
  have h := Finset.single_le_sum
    (f := fun j => if f j = f i then (Fintype.card ι : ℝ)⁻¹ else 0)
    (fun j (_ : j ∈ Finset.univ) => by split_ifs <;> positivity) (Finset.mem_univ i)
  simp only [ite_true] at h
  exact lt_of_lt_of_le (by positivity) h


lemma sum_over_embedding_le {ι α : Type*} [Fintype ι] [Fintype α]
    (e : ι ↪ α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    ∑ i, f (e i) ≤ ∑ a, f a := by
  rw [← Finset.sum_image (fun i _ j _ hij => e.injective hij)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun a _ _ => hf a)

/-- The exact exp(number of holes) product loss. The marginals are computed
from the actual occupied embedding, so arbitrary deletion patterns are covered.
This is the entropy/quarter-root normalization step of weighted.tex:143–150
and coherent.tex:191–205. -/
theorem occupied_product_of_mean_le {ι α β : Type*}
    [Fintype ι] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (e : ι ↪ α × β) (z : α → β → ℝ) (hz : ∀ a b, 0 ≤ z a b)
    (hmean : ∑ a, ∑ b,
      uniformMarginal (fun i => (e i).1) a * uniformMarginal (fun i => (e i).2) b * z a b ≤ 1) :
    ∏ i, z (e i).1 (e i).2 ≤
      Real.exp ((Fintype.card α * Fintype.card β - Fintype.card ι : ℕ) : ℝ) := by
  classical
  by_cases hempty : IsEmpty ι
  · let := hempty
    simp only [Fintype.prod_empty]
    exact Real.one_le_exp (Nat.cast_nonneg _)
  have : Nonempty ι := not_isEmpty_iff.mp hempty
  by_cases hz0 : ∃ i, z (e i).1 (e i).2 = 0
  · obtain ⟨i, hi⟩ := hz0
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hi]
    exact (Real.exp_pos _).le
  have hzpos : ∀ i, 0 < z (e i).1 (e i).2 := by
    intro i
    exact lt_of_le_of_ne (hz _ _) (Ne.symm (fun h => hz0 ⟨i, h⟩))
  let p := uniformMarginal (fun i => (e i).1)
  let q := uniformMarginal (fun i => (e i).2)
  let s : ℝ := Fintype.card ι
  have hs : 0 < s := by dsimp [s]; positivity
  have hp : ∀ i, 0 < p (e i).1 := uniformMarginal_pos _
  have hq : ∀ i, 0 < q (e i).2 := uniformMarginal_pos _
  have hps : ∑ a, p a = 1 := sum_uniformMarginal _
  have hqs : ∑ b, q b = 1 := sum_uniformMarginal _
  have hpe := entropy_le_log_card p (uniformMarginal_nonneg _) hps
  have hqe := entropy_le_log_card q (uniformMarginal_nonneg _) hqs
  have hmean' : ∑ i, p (e i).1 * q (e i).2 * z (e i).1 (e i).2 ≤ 1 := by
    apply (sum_over_embedding_le e (fun x => p x.1 * q x.2 * z x.1 x.2) ?_).trans
    · simpa only [Fintype.sum_prod_type] using hmean
    · intro x
      exact mul_nonneg (mul_nonneg (uniformMarginal_nonneg _ _) (uniformMarginal_nonneg _ _)) (hz _ _)
  have hlogs : ∑ i, Real.log (s * p (e i).1 * q (e i).2 * z (e i).1 (e i).2) ≤ 0 := by
    calc
      _ ≤ ∑ i, (s * (p (e i).1 * q (e i).2 * z (e i).1 (e i).2) - 1) := by
        apply Finset.sum_le_sum
        intro i _
        have hh := Real.log_le_sub_one_of_pos (mul_pos (mul_pos (mul_pos hs (hp i)) (hq i)) (hzpos i))
        simpa only [mul_assoc] using hh
      _ = s * (∑ i, p (e i).1 * q (e i).2 * z (e i).1 (e i).2) - s := by
        simp [Finset.sum_sub_distrib, ← Finset.mul_sum, s]
      _ ≤ 0 := by nlinarith
  have hlogexpand : ∑ i, Real.log (s * p (e i).1 * q (e i).2 * z (e i).1 (e i).2) =
      s * Real.log s + (∑ i, Real.log (p (e i).1)) + (∑ i, Real.log (q (e i).2)) +
        ∑ i, Real.log (z (e i).1 (e i).2) := by
    simp_rw [Real.log_mul (ne_of_gt (mul_pos (mul_pos hs (hp _)) (hq _))) (ne_of_gt (hzpos _)),
      Real.log_mul (ne_of_gt (mul_pos hs (hp _))) (ne_of_gt (hq _)),
      Real.log_mul (ne_of_gt hs) (ne_of_gt (hp _))]
    simp [Finset.sum_add_distrib, s]
  rw [hlogexpand] at hlogs
  have hplog : ∑ i, Real.log (p (e i).1) = s * ∑ a, p a * Real.log (p a) := by
    have h := sum_uniformMarginal_mul (fun i => (e i).1) (fun a => Real.log (p a))
    change _ = s⁻¹ * _ at h
    rw [h, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hs), one_mul]
  have hqlog : ∑ i, Real.log (q (e i).2) = s * ∑ b, q b * Real.log (q b) := by
    have h := sum_uniformMarginal_mul (fun i => (e i).2) (fun b => Real.log (q b))
    change _ = s⁻¹ * _ at h
    rw [h, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hs), one_mul]
  rw [hplog, hqlog] at hlogs
  have hlogbound : ∑ i, Real.log (z (e i).1 (e i).2) ≤
      s * (Real.log (Fintype.card α) + Real.log (Fintype.card β) - Real.log s) := by
    nlinarith [mul_le_mul_of_nonneg_left hpe hs.le, mul_le_mul_of_nonneg_left hqe hs.le]
  have hm : (0 : ℝ) < Fintype.card α := by
    have : Nonempty α := ⟨(e (Classical.choice inferInstance)).1⟩
    positivity
  have hn : (0 : ℝ) < Fintype.card β := by
    have : Nonempty β := ⟨(e (Classical.choice inferInstance)).2⟩
    positivity
  have hfrac := Real.log_le_sub_one_of_pos (div_pos (mul_pos hm hn) hs)
  rw [Real.log_div (ne_of_gt (mul_pos hm hn)) (ne_of_gt hs),
    Real.log_mul (ne_of_gt hm) (ne_of_gt hn)] at hfrac
  have hcancel : s * ((Fintype.card α : ℝ) * Fintype.card β / s - 1) =
      (Fintype.card α : ℝ) * Fintype.card β - s := by field_simp
  have hfinite : Fintype.card ι ≤ Fintype.card α * Fintype.card β := by
    simpa using Fintype.card_le_of_injective e e.injective
  have hfinal : ∑ i, Real.log (z (e i).1 (e i).2) ≤
      ((Fintype.card α * Fintype.card β - Fintype.card ι : ℕ) : ℝ) := by
    rw [Nat.cast_sub hfinite, Nat.cast_mul]
    have h := mul_le_mul_of_nonneg_left hfrac hs.le
    rw [hcancel] at h
    exact hlogbound.trans h
  calc
    _ = Real.exp (∑ i, Real.log (z (e i).1 (e i).2)) := by
      rw [Real.exp_sum]
      exact Finset.prod_congr rfl (fun i _ => (Real.exp_log (hzpos i)).symm)
    _ ≤ _ := Real.exp_le_exp.mpr hfinal

end RowColumn

end
end

end OAI
end

section
-- module Solutions.OAIW2_RowColumn.RowColumn_TensorFilter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
open FiniteStarAlgebra Signed
variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]

omit [DecidableEq C] in
lemma hsVector_tensor_norm_sq (M : S → Matrix C C ℂ) :
    ‖hsVector (tensorMatrix M)‖^2 = ∏ i, ‖hsVector (M i)‖^2 := by
  rw [hsVector_norm_sq, tensorMatrix_star, tensorMatrix_mul, tensorMatrix_trace]
  simp_rw [← hsVector_inner, inner_self_eq_norm_sq_to_K]
  change (∏ i, ((‖hsVector (M i)‖ : ℝ) : ℂ)^2).re = _
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_prod, Complex.ofReal_re]

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
lemma sectorTensor_hermitian (odd : C → Prop) [DecidablePred odd] (k : ℕ)
    (M : S → Matrix C C ℂ) (hM : ∀ i, (M i).IsHermitian) :
    (sectorTensor odd k M).IsHermitian := by
  change star (sectorTensor odd k M) = sectorTensor odd k M
  rw [← sectorTensor_star]
  congr 1
  funext i
  exact hM i

lemma sectorTensor_positive (odd : C → Prop) [DecidablePred odd] (k : ℕ)
    (M : S → Matrix C C ℂ) (hM : ∀ i, (M i).PosSemidef) :
    (sectorTensor odd k M).PosSemidef :=
  (tensorMatrix_posSemidef M hM).submatrix _

lemma sectorTensor_root_square (odd : C → Prop) [DecidablePred odd] (k : ℕ)
    (M : S → Matrix C C ℂ) (hM : ∀ i, (M i).PosSemidef)
    (he : ∀ i, M i ∈ evenAlgebra odd) :
    sectorTensor odd k (fun i => CFC.sqrt (M i)) ^ 2 = sectorTensor odd k M := by
  rw [pow_two, ← sectorTensor_mul odd k _ _ (fun i => sqrt_even odd (M i) (hM i) (he i))]
  congr 1
  funext i
  exact CFC.sqrt_mul_sqrt_self _ (hM i).nonneg

/-- The restriction is taken only after factoring the positive weighted
Hilbert--Schmidt norm. In particular no diagonal of a nonpositive product is
compared to the full trace. -/
lemma sector_unitary_sandwich_bound (odd : C → Prop) [DecidablePred odd] (k : ℕ)
    (M N : S → Matrix C C ℂ) (U : Matrix C C ℂ)
    (hM : ∀ i, (M i).PosSemidef) (hN : ∀ i, (N i).PosSemidef)
    (heM : ∀ i, M i ∈ evenAlgebra odd) (_ : ∀ i, N i ∈ evenAlgebra odd)
    (heU : U ∈ evenAlgebra odd) :
    ‖hsVector (sectorTensor odd k (fun i => CFC.sqrt (M i)) *
      sectorTensor odd k (fun _ : S => U) *
      sectorTensor odd k (fun i => CFC.sqrt (N i)))‖^2 ≤
        ∏ i, (M i * U * N i * U.conjTranspose).trace.re := by
  rw [← sectorTensor_mul odd k _ _ (fun i => sqrt_even odd (M i) (hM i) (heM i))]
  rw [← sectorTensor_mul odd k _ _ (fun i => (evenAlgebra odd).mul_mem
    (sqrt_even odd (M i) (hM i) (heM i)) heU)]
  let e : Words (S := S) odd k ↪ (S → C) := ⟨Subtype.val, Subtype.val_injective⟩
  have hb := hsVector_submatrix_norm_sq_le e e
    (tensorMatrix (fun i => CFC.sqrt (M i) * U * CFC.sqrt (N i)))
  change ‖hsVector (sectorTensor odd k _)‖^2 ≤ _ at hb
  rw [hsVector_tensor_norm_sq] at hb
  convert hb using 1
  apply Finset.prod_congr rfl
  intro i _
  rw [hsVector_sandwich_sq _ _ U
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (M i))).isHermitian
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (N i))).isHermitian]
  rw [CFC.sq_sqrt (M i) (hM i).nonneg, CFC.sq_sqrt (N i) (hN i).nonneg]

/-- Use the intrinsic spectral order on the closed finite C*-algebra. Its
physical Hilbert--Schmidt structure and existing operator norm are unchanged. -/
lemma algebra_reconstruction_hilbert_bound
    {E H G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Group G]
    (A : StarSubalgebra ℂ (E →L[ℂ] E)) (u : G →* unitary A)
    (hspan : Submodule.span ℂ (Set.range fun g : G => (u g : A)) = ⊤)
    (B : A) (F : A →ₗ[ℂ] H) (R : ℝ) (hR : 0 ≤ R)
    (hU : ∀ g, ‖F (u g : A)‖ ≤ R) :
    ‖F B‖ ≤ 4 * (Module.finrank ℂ A : ℝ) * ‖B‖ * R := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  exact UnitaryFrame.reconstruction_hilbert_bound (physicalTrace A) (algebraCore A)
    (core_inner_trace A) u hspan B F R hR hU

lemma sector_unitary_matrix (odd : C → Prop) [DecidablePred odd] (k : ℕ)
    (U : unitary (evenAlgebra odd)) :
    algebraMatrix (sectorAlgebra (S := S) odd k)
      (unitarySpanHom (R := ℂ) (sectorUnitary (S := S) odd k) U).val = sectorTensor odd k (fun _ : S => U.val.val) := by
  exact (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm_apply_apply _

/-- Weighted reconstruction in the actual signed sector, with the exact
occupied-board entropy loss and singular quarter-root normalization. -/
theorem whitened_reconstruction_bound {L K : Type*} [Fintype L] [Fintype K]
    [DecidableEq L] [DecidableEq K] [Nonempty S]
    (odd : C → Prop) [DecidablePred odd] (k : ℕ) (e : S ↪ L × K)
    (M : L → Matrix C C ℂ) (N : K → Matrix C C ℂ)
    (hM : ∀ i, (M i).PosSemidef) (hN : ∀ j, (N j).PosSemidef)
    (heM : ∀ i, M i ∈ evenAlgebra odd) (heN : ∀ j, N j ∈ evenAlgebra odd)
    (hMt : ∀ i, (M i).trace.re ≤ 1) (hNt : ∀ j, (N j).trace.re ≤ 1)
    (B : sectorAlgebra (S := S) odd k) :
    let p := uniformMarginal (fun i => (e i).1)
    let q := uniformMarginal (fun i => (e i).2)
    let M' := fun i => whitenState (stateMean p M) (M i)
    let N' := fun j => whitenState (stateMean q N) (N j)
    ‖hsVector (sectorTensor odd k (fun i => CFC.sqrt (M' (e i).1)) *
      algebraMatrix (sectorAlgebra (S := S) odd k) B *
      sectorTensor odd k (fun i => CFC.sqrt (N' (e i).2)))‖^2 ≤
      16 * (Module.finrank ℂ (sectorAlgebra (S := S) odd k) : ℝ)^2 * ‖B‖^2 *
        Real.exp ((Fintype.card L * Fintype.card K - Fintype.card S : ℕ) : ℝ) := by
  dsimp only
  let p := uniformMarginal (fun i => (e i).1)
  let q := uniformMarginal (fun i => (e i).2)
  let M' := fun i => whitenState (stateMean p M) (M i)
  let N' := fun j => whitenState (stateMean q N) (N j)
  let A := sectorAlgebra (S := S) odd k
  let R := Real.exp ((Fintype.card L * Fintype.card K - Fintype.card S : ℕ) : ℝ)
  let F := sandwichMap A (sectorTensor odd k (fun i => CFC.sqrt (M' (e i).1)))
    (sectorTensor odd k (fun i => CFC.sqrt (N' (e i).2)))
  have hp := uniformMarginal_nonneg (fun i => (e i).1)
  have hq := uniformMarginal_nonneg (fun i => (e i).2)
  have hMp : ∀ i, (M' i).PosSemidef := fun i => whitenState_positive _ _ (hM i)
  have hNp : ∀ j, (N' j).PosSemidef := fun j => whitenState_positive _ _ (hN j)
  have hMe : ∀ i, M' i ∈ evenAlgebra odd := fun i =>
    whitenState_even odd _ _ (stateMean_positive p M hp hM) (stateMean_even odd p M heM) (heM i)
  have hNe : ∀ j, N' j ∈ evenAlgebra odd := fun j =>
    whitenState_even odd _ _ (stateMean_positive q N hq hN) (stateMean_even odd q N heN) (heN j)
  have hu (U : unitary (evenAlgebra odd)) :
      ‖F (unitarySpanHom (R := ℂ) (sectorUnitary (S := S) odd k) U).val‖ ≤ Real.sqrt R := by
    apply Real.le_sqrt_of_sq_le
    change ‖hsVector (sectorTensor odd k (fun i => CFC.sqrt (M' (e i).1)) *
      algebraMatrix (sectorAlgebra (S := S) odd k)
        (unitarySpanHom (R := ℂ) (sectorUnitary (S := S) odd k) U).val *
      sectorTensor odd k (fun i => CFC.sqrt (N' (e i).2)))‖^2 ≤ R
    rw [sector_unitary_matrix]
    apply (sector_unitary_sandwich_bound odd k (fun i => M' (e i).1) (fun i => N' (e i).2)
      U.val.val (fun i => hMp _) (fun i => hNp _) (fun i => hMe _) (fun i => hNe _)
      U.val.property).trans
    apply occupied_product_of_mean_le e (fun i j => (M' i * U.val.val * N' j * U.val.val.conjTranspose).trace.re)
    · exact fun i j => local_overlap_nonneg _ _ _ (hMp i) (hNp j)
    · exact weighted_whitened_mean_le_one p q M N hp hq (sum_uniformMarginal _)
        (sum_uniformMarginal _) hM hN hMt hNt U.val.val
        ⟨congrArg Subtype.val U.property.1, congrArg Subtype.val U.property.2⟩
  have hh := algebra_reconstruction_hilbert_bound A
    (unitarySpanHom (R := ℂ) (sectorUnitary (S := S) odd k))
    (unitarySpanHom_spans (R := ℂ) (sectorUnitary (S := S) odd k)) B F
    (Real.sqrt R) (Real.sqrt_nonneg _) hu
  have hs := pow_le_pow_left₀ (norm_nonneg (F B)) hh 2
  change ‖F B‖^2 ≤ _
  calc
    _ ≤ (4 * (Module.finrank ℂ A : ℝ) * ‖B‖ * Real.sqrt R)^2 := hs
    _ = _ := by
      dsimp only [A, R]
      simp only [mul_pow, Real.sq_sqrt (le_of_lt (Real.exp_pos _))]
      ring

lemma filtered_trace_identity {I : Type*} [Fintype I] [DecidableEq I]
    (A B R T F G Q : Matrix I I ℂ)
    (hR : R.IsHermitian) (hT : T.IsHermitian)
    (hF : F.IsHermitian) (hG : G.IsHermitian) (hQ : Q.IsHermitian)
    (hA : F * R^2 * F = A) (hB : G * T^2 * G = B) :
    (A * Q * B * Q).trace.re = ‖hsVector (R * (F * Q * G) * T)‖^2 := by
  rw [hsVector_sandwich_sq R T _ hR hT]
  simp only [Matrix.conjTranspose_mul, hF.eq, hG.eq, hQ.eq]
  rw [← hA, ← hB]
  apply congrArg Complex.re
  calc
    _ = (F * (R^2 * F * Q * G * T^2 * G * Q)).trace := by simp only [mul_assoc]
    _ = ((R^2 * F * Q * G * T^2 * G * Q) * F).trace := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [mul_assoc]

end RowColumn.MatrixState

end
end


section

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
open FiniteStarAlgebra Signed
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma algebraMatrix_mul (A : StarSubalgebra ℂ (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I))
    (a b : A) : algebraMatrix A (a*b) = algebraMatrix A a * algebraMatrix A b :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm.map_mul a.val b.val
lemma algebraMatrix_star (A : StarSubalgebra ℂ (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I))
    (a : A) : algebraMatrix A (star a) = star (algebraMatrix A a) :=
  (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)).symm.map_star' a.val
lemma algebraMatrix_hermitian (A : StarSubalgebra ℂ (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I))
    (a : A) (ha : star a=a) : (algebraMatrix A a).IsHermitian := by
  change star (algebraMatrix A a)=_
  rw [← algebraMatrix_star, ha]
lemma algebraMatrix_trace (A : StarSubalgebra ℂ (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I))
    (a : A) : (algebraMatrix A a).trace = physicalTrace A a := by
  rw [← trace_toEuclideanCLM]
  change LinearMap.trace ℂ (EuclideanSpace ℂ I)
    ((Matrix.toEuclideanCLM (𝕜 := ℂ)) ((Matrix.toEuclideanCLM (𝕜 := ℂ)).symm a.val)).toLinearMap = _
  rw [(Matrix.toEuclideanCLM (𝕜 := ℂ)).apply_symm_apply]
  rfl

variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]

lemma tensorMatrix_trace_re (M : S → Matrix C C ℂ) (hM : ∀ i, (M i).PosSemidef) :
    (tensorMatrix M).trace.re = ∏ i, (M i).trace.re := by
  have hs (i : S) : (CFC.sqrt (M i)).conjTranspose * CFC.sqrt (M i) = M i := by
    rw [(Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (M i))).isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self _ (hM i).nonneg
  have ht := hsVector_tensor_norm_sq (fun i => CFC.sqrt (M i))
  simp only [hsVector_norm_sq, tensorMatrix_star, tensorMatrix_mul, hs] at ht
  exact ht

lemma sectorTensor_trace_le (odd : C → Prop) [DecidablePred odd] (k : ℕ)
    (M : S → Matrix C C ℂ) (hM : ∀ i, (M i).PosSemidef) :
    (sectorTensor odd k M).trace.re ≤ (tensorMatrix M).trace.re := by
  let e : Words (S := S) odd k ↪ (S → C) := ⟨Subtype.val, Subtype.val_injective⟩
  have hh := finite_sum_embedding_le e (fun w => (tensorMatrix M w w).re)
    (fun w => ((tensorMatrix_posSemidef M hM).diag_nonneg (i := w)).1)
  simpa only [sectorTensor, Matrix.trace, Matrix.diag, Complex.re_sum, Matrix.submatrix_apply, e, Function.Embedding.coeFn_mk] using hh

lemma sectorTensor_substate_trace (odd : C → Prop) [DecidablePred odd] (k : ℕ)
    (M : S → Matrix C C ℂ) (hM : ∀ i, (M i).PosSemidef)
    (htr : ∀ i, (M i).trace.re ≤ 1) : (sectorTensor odd k M).trace.re ≤ 1 := by
  apply (sectorTensor_trace_le odd k M hM).trans
  rw [tensorMatrix_trace_re M hM]
  exact Finset.prod_le_one (fun i _ => (hM i).trace_nonneg.1) (fun i _ => htr i)

lemma positiveTensor_matrix (odd : C → Prop) [DecidablePred odd] (k : ℕ)
    (M : Matrix C C ℂ) (hM : M.PosSemidef) (he : M ∈ evenAlgebra odd) :
    algebraMatrix (sectorAlgebra (S := S) odd k) (positiveTensor odd k M hM he) =
      sectorTensor odd k (fun _ : S => M) :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm_apply_apply _

lemma positiveTensor_isPositive (odd : C → Prop) [DecidablePred odd] (k : ℕ)
    (M : Matrix C C ℂ) (hM : M.PosSemidef) (he : M ∈ evenAlgebra odd) :
    (positiveTensor (S := S) odd k M hM he).val.IsPositive :=
  (toEuclideanCLM_positive_iff _).mpr (sectorTensor_positive odd k _ (fun _ : S => hM))

lemma positiveTensor_selfAdjoint (odd : C → Prop) [DecidablePred odd] (k : ℕ)
    (M : Matrix C C ℂ) (hM : M.PosSemidef) (he : M ∈ evenAlgebra odd) :
    IsSelfAdjoint (positiveTensor (S := S) odd k M hM he) := by
  apply Subtype.ext
  exact (positiveTensor_isPositive odd k M hM he).isSelfAdjoint

lemma positiveTensor_trace_le_one (odd : C → Prop) [DecidablePred odd] (k : ℕ)
    (M : Matrix C C ℂ) (hM : M.PosSemidef) (he : M ∈ evenAlgebra odd) (htr : M.trace.re ≤ 1) :
    (physicalTrace (sectorAlgebra (S := S) odd k) (positiveTensor odd k M hM he)).re ≤ 1 := by
  rw [← algebraMatrix_trace, positiveTensor_matrix]
  exact sectorTensor_substate_trace odd k _ (fun _ : S => hM) (fun _ => htr)

lemma positiveTensor_quarter_four (odd : C → Prop) [DecidablePred odd] (k : ℕ)
    (M : Matrix C C ℂ) (hM : M.PosSemidef) (he : M ∈ evenAlgebra odd) :
    positiveTensor (S := S) odd k (quarterRoot M) (quarter_positive M) (quarter_even odd M hM he) ^ 4 =
      positiveTensor odd k M hM he := by
  apply Subtype.ext
  change (Matrix.toEuclideanCLM (𝕜 := ℂ) (sectorTensor odd k (fun _ : S => quarterRoot M)))^4 = _
  rw [← map_pow]
  have hh := (sectorPowerHom (S := S) odd k).map_pow
    (⟨quarterRoot M, quarter_even odd M hM he⟩ : evenAlgebra odd) 4
  change sectorTensor odd k (fun _ : S => quarterRoot M ^ 4) =
    (sectorTensor odd k (fun _ : S => quarterRoot M)) ^ 4 at hh
  rw [← hh, quarter_four M hM]
  rfl

/-- The actual irreducible-dimension filter acts on fourth powers of both
mean-state tensors. Its quarter-root sandwich has squared norm at most 1/d. -/
theorem quarter_tensor_filter_bound (odd : C → Prop) [DecidablePred odd] (k : ℕ)
    (q : sectorAlgebra (S := S) odd k) (hqs : star q=q) (hqq : q*q=q)
    (hqc : ∀ a, q*a=a*q) (d : ℝ) (hd : 0<d)
    (hfilter : ∀ a : sectorAlgebra (S := S) odd k, a.val.IsPositive →
      ‖q*a‖ ≤ (physicalTrace (sectorAlgebra (S := S) odd k) a).re / d)
    (M N : Matrix C C ℂ) (hM : M.PosSemidef) (hN : N.PosSemidef)
    (heM : M ∈ evenAlgebra odd) (heN : N ∈ evenAlgebra odd)
    (hMt : M.trace.re ≤ 1) (hNt : N.trace.re ≤ 1) :
    ‖positiveTensor odd k (quarterRoot M) (quarter_positive M) (quarter_even odd M hM heM) * q *
      positiveTensor odd k (quarterRoot N) (quarter_positive N) (quarter_even odd N hN heN)‖^2 ≤ 1/d := by
  apply filterNorm_sq q _ _ hqs hqq
    (positiveTensor_selfAdjoint odd k _ _ _) (positiveTensor_selfAdjoint odd k _ _ _)
    (hqc _) (hqc _) d hd
  · rw [positiveTensor_quarter_four odd k M hM heM]
    apply (hfilter _ (positiveTensor_isPositive odd k M hM heM)).trans
    exact div_le_div_of_nonneg_right (positiveTensor_trace_le_one odd k M hM heM hMt) hd.le
  · rw [positiveTensor_quarter_four odd k N hN heN]
    apply (hfilter _ (positiveTensor_isPositive odd k N hN heN)).trans
    exact div_le_div_of_nonneg_right (positiveTensor_trace_le_one odd k N hN heN hNt) hd.le

lemma sector_unwhiten_identity {L : Type*} [Fintype L] [DecidableEq L] [Nonempty S]
    (odd : C → Prop) [DecidablePred odd] (k : ℕ) (line : S → L)
    (M : L → Matrix C C ℂ) (hM : ∀ i, (M i).PosSemidef)
    (heM : ∀ i, M i ∈ evenAlgebra odd) :
    let p := uniformMarginal line
    let A := stateMean p M
    let M' := fun i => whitenState A (M i)
    sectorTensor odd k (fun _ : S => quarterRoot A) *
      sectorTensor odd k (fun x => CFC.sqrt (M' (line x))) ^ 2 *
      sectorTensor odd k (fun _ : S => quarterRoot A) =
      sectorTensor odd k (fun x => M (line x)) := by
  dsimp only
  let p := uniformMarginal line
  let A := stateMean p M
  let M' := fun i => whitenState A (M i)
  have hp := uniformMarginal_nonneg line
  have hA := stateMean_positive p M hp hM
  have heA := stateMean_even odd p M heM
  have hMp : ∀ i, (M' i).PosSemidef := fun i => whitenState_positive A (M i) (hM i)
  have hMe : ∀ i, M' i ∈ evenAlgebra odd := fun i => whitenState_even odd A (M i) hA heA (heM i)
  change sectorTensor odd k (fun _ : S => quarterRoot A) *
    sectorTensor odd k (fun x => CFC.sqrt (M' (line x))) ^ 2 *
    sectorTensor odd k (fun _ : S => quarterRoot A) = _
  rw [sectorTensor_root_square odd k _ (fun x => hMp _) (fun x => hMe _)]
  rw [← sectorTensor_mul odd k _ _ (fun _ => quarter_even odd A hA heA)]
  rw [← sectorTensor_mul odd k _ _ (fun x => (evenAlgebra odd).mul_mem
    (quarter_even odd A hA heA) (hMe _))]
  congr 1
  funext x
  exact unwhitenState p M hp hM (line x) (uniformMarginal_pos line x)

/-- The quantitative global bridge: two arbitrary admissible fibre-product
substates, on the actual signed sector and the actual central isotypic filter.
No invertibility, sector-surrogate, or postselection bound is assumed. -/
theorem sector_filtered_trace_bound_oai {L K : Type*} [Fintype L] [Fintype K]
    [DecidableEq L] [DecidableEq K] [Nonempty S]
    (odd : C → Prop) [DecidablePred odd] (k : ℕ) (e : S ↪ L × K)
    (q : sectorAlgebra (S := S) odd k) (hqs : star q=q) (hqq : q*q=q)
    (hqc : ∀ a, q*a=a*q) (d : ℝ) (hd : 0<d)
    (hfilter : ∀ a : sectorAlgebra (S := S) odd k, a.val.IsPositive →
      ‖q*a‖ ≤ (physicalTrace (sectorAlgebra (S := S) odd k) a).re / d)
    (M : L → Matrix C C ℂ) (N : K → Matrix C C ℂ)
    (hM : ∀ i, (M i).PosSemidef) (hN : ∀ j, (N j).PosSemidef)
    (heM : ∀ i, M i ∈ evenAlgebra odd) (heN : ∀ j, N j ∈ evenAlgebra odd)
    (hMt : ∀ i, (M i).trace.re ≤ 1) (hNt : ∀ j, (N j).trace.re ≤ 1) :
    (sectorTensor odd k (fun x => M (e x).1) * algebraMatrix (sectorAlgebra (S := S) odd k) q *
      sectorTensor odd k (fun x => N (e x).2) * algebraMatrix (sectorAlgebra (S := S) odd k) q).trace.re ≤
      16 * (Module.finrank ℂ (sectorAlgebra (S := S) odd k) : ℝ)^2 *
        Real.exp ((Fintype.card L * Fintype.card K - Fintype.card S : ℕ) : ℝ) / d := by
  let p := uniformMarginal (fun x => (e x).1)
  let r := uniformMarginal (fun x => (e x).2)
  let A := stateMean p M
  let B := stateMean r N
  let M' := fun i => whitenState A (M i)
  let N' := fun j => whitenState B (N j)
  have hp := uniformMarginal_nonneg (fun x => (e x).1)
  have hr := uniformMarginal_nonneg (fun x => (e x).2)
  have hA := stateMean_positive p M hp hM
  have hB := stateMean_positive r N hr hN
  have heA := stateMean_even odd p M heM
  have heB := stateMean_even odd r N heN
  let F := positiveTensor (S := S) odd k (quarterRoot A) (quarter_positive A) (quarter_even odd A hA heA)
  let G := positiveTensor (S := S) odd k (quarterRoot B) (quarter_positive B) (quarter_even odd B hB heB)
  have hnorm : ‖F*q*G‖^2 ≤ 1/d := quarter_tensor_filter_bound odd k q hqs hqq hqc d hd hfilter
    A B hA hB heA heB (stateMean_trace_le_one p M hp (sum_uniformMarginal _) hMt)
    (stateMean_trace_le_one r N hr (sum_uniformMarginal _) hNt)
  have hrec := whitened_reconstruction_bound odd k e M N hM hN heM heN hMt hNt (F*q*G)
  change ‖hsVector (sectorTensor odd k (fun x => CFC.sqrt (M' (e x).1)) *
    algebraMatrix (sectorAlgebra (S := S) odd k) (F*q*G) *
    sectorTensor odd k (fun x => CFC.sqrt (N' (e x).2)))‖^2 ≤ _ at hrec
  simp only [algebraMatrix_mul, F, G, positiveTensor_matrix] at hrec
  have hi := filtered_trace_identity
    (sectorTensor odd k (fun x => M (e x).1)) (sectorTensor odd k (fun x => N (e x).2))
    (sectorTensor odd k (fun x => CFC.sqrt (M' (e x).1)))
    (sectorTensor odd k (fun x => CFC.sqrt (N' (e x).2)))
    (sectorTensor odd k (fun _ : S => quarterRoot A))
    (sectorTensor odd k (fun _ : S => quarterRoot B))
    (algebraMatrix (sectorAlgebra (S := S) odd k) q)
    (sectorTensor_hermitian odd k _ (fun x => (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).isHermitian))
    (sectorTensor_hermitian odd k _ (fun x => (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).isHermitian))
    (sectorTensor_hermitian odd k _ (fun _ => (quarter_positive A).isHermitian))
    (sectorTensor_hermitian odd k _ (fun _ => (quarter_positive B).isHermitian))
    (algebraMatrix_hermitian _ q hqs)
    (sector_unwhiten_identity odd k (fun x => (e x).1) M hM heM)
    (sector_unwhiten_identity odd k (fun x => (e x).2) N hN heN)
  rw [hi]
  apply hrec.trans
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hnorm
      (by positivity : 0 ≤ 16 * (Module.finrank ℂ (sectorAlgebra (S := S) odd k) : ℝ)^2))
    (le_of_lt (Real.exp_pos ((Fintype.card L * Fintype.card K - Fintype.card S : ℕ) : ℝ)))
  convert hh using 1; ring

end RowColumn.MatrixState

end
end

end OAI
end

theorem solution.{u_2, u_3, u_4, u_5} : type_of% @OAI.RowColumn.MatrixState.sector_filtered_trace_bound_oai.{u_2, u_3, u_4, u_5} := @OAI.RowColumn.MatrixState.sector_filtered_trace_bound_oai.{u_2, u_3, u_4, u_5}

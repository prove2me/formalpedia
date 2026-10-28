-- Prove2me | solution 1 for OAI.Heisenberg.spontaneous_magnetization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T08:47:09.911095+00:00
-- url     : https://prove2.me/submissions/f68947c1-9460-42a4-9310-557aa7abf1e0

import Mathlib
import Definitions.Def_Heisenberg
import Definitions.Def_OAIW2HM002
import Theorems.Thm_OAI_Heisenberg_Selection_field_ordered_cubes
import Theorems.Thm_OAI_Heisenberg_cubeAverage_limit_KMS
import Theorems.Thm_OAI_Heisenberg_dynamics_converges

section
-- module Solutions.OAIW2_Heis.Heisenberg_LocalDynamics
attribute [-instance] _root_.OAI.Heisenberg.quasiLocalClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical
open scoped ComplexConjugate BigOperators

namespace Heisenberg

theorem eventually_mem_box {d : ℕ} (x : Site d) :
    ∀ᶠ n : ℕ in Filter.atTop, x ∈ box d n := by
  have hl (i : Fin d) : ∀ᶠ n : ℕ in Filter.atTop, (x i).natAbs ≤ n :=
    Filter.eventually_ge_atTop _
  have hh := (Filter.eventually_all).mpr hl
  filter_upwards [hh] with n hn
  simp only [box, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have h := hn i
  have hcast : ((x i).natAbs : ℤ) ≤ n := by exact_mod_cast h
  exact abs_le.mp (by simpa only [Int.natCast_natAbs] using hcast)

theorem localCore_dense (d ℓ : ℕ) : Dense (localCore d ℓ : Set (QuasiLocal d ℓ)) := by
  let B := StarAlgebra.adjoin ℂ {A : SpinOperator d ℓ | ∃ x a b, A = matrixUnit d ℓ x a b}
  let f : B →⋆ₐ[ℂ] QuasiLocal d ℓ := StarSubalgebra.inclusion B.le_topologicalClosure
  have hd : DenseRange f := by
    change DenseRange (Set.inclusion B.le_topologicalClosure)
    apply (denseRange_inclusion_iff B.le_topologicalClosure).mpr
    rw [StarSubalgebra.topologicalClosure_coe]
  have hle : B ≤ (localCore d ℓ).map (quasiLocalAlgebra d ℓ).subtype := by
    apply StarAlgebra.adjoin_le
    rintro A ⟨x,a,b,rfl⟩
    exact ⟨localUnit d ℓ x a b, StarAlgebra.subset_adjoin ℂ _ ⟨x,a,b,rfl⟩, rfl⟩
  apply Dense.mono (s₁ := Set.range f) ?_ hd
  rintro A ⟨a,rfl⟩
  obtain ⟨b,hb,he⟩ := hle a.property
  have heq : f a = b := Subtype.ext he.symm
  rwa [heq]

end Heisenberg

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_StateCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical
open scoped ComplexConjugate BigOperators
open Filter Topology Metric
open scoped NNReal
open scoped NNReal

namespace Heisenberg

theorem countable_monoidClosure {M : Type*} [Monoid M] {s : Set M}
    (hs : s.Countable) : (Submonoid.closure s : Set M).Countable := by
  have : Countable s := hs.to_subtype
  let f : List s → M := fun l => (l.map Subtype.val).prod
  apply (Set.countable_range f).mono
  intro x hx
  induction hx using Submonoid.closure_induction with
  | mem x hx => exact ⟨[⟨x, hx⟩], by simp [f]⟩
  | one => exact ⟨[], rfl⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨l, rfl⟩ := ihx
    obtain ⟨k, rfl⟩ := ihy
    exact ⟨l ++ k, by simp [f]⟩

instance quasiLocalSeparable (d ℓ : ℕ) : TopologicalSpace.SeparableSpace (QuasiLocal d ℓ) := by
  let s : Set (SpinOperator d ℓ) := {A | ∃ x a b, A = matrixUnit d ℓ x a b}
  have hs : s.Countable := by
    have h := Set.countable_range (fun p : Site d × Level ℓ × Level ℓ =>
      matrixUnit d ℓ p.1 p.2.1 p.2.2)
    apply h.mono
    rintro A ⟨x, a, b, rfl⟩
    exact ⟨⟨x,a,b⟩, rfl⟩
  have hu : (s ∪ star s).Countable := hs.union (by simpa only [Set.image_star] using hs.image star)
  have hsep := (countable_monoidClosure hu).isSeparable.span (R := ℂ)
  have hadj : TopologicalSpace.IsSeparable (StarAlgebra.adjoin ℂ s : Set (SpinOperator d ℓ)) := by
    change TopologicalSpace.IsSeparable
      ((StarAlgebra.adjoin ℂ s).toSubalgebra.toSubmodule : Set (SpinOperator d ℓ))
    rw [StarAlgebra.adjoin_eq_span]
    exact hsep
  have hc : TopologicalSpace.IsSeparable (quasiLocalAlgebra d ℓ : Set (SpinOperator d ℓ)) := by
    change TopologicalSpace.IsSeparable ((StarAlgebra.adjoin ℂ s).topologicalClosure : Set (SpinOperator d ℓ))
    rw [StarSubalgebra.topologicalClosure_coe]
    exact hadj.closure
  exact hc.separableSpace

open scoped ComplexOrder

theorem positive_norm_bound {E : Type*} [CStarAlgebra E] [PartialOrder E]
    [StarOrderedRing E] (φ : E →L[ℂ] ℂ) (hn : φ 1 = 1)
    (hpos : ∀ B, 0 ≤ φ (star B * B)) : ‖φ‖ ≤ 4 := by
  have hp : ∀ A : E, 0 ≤ A → 0 ≤ φ A := by
    intro A hA
    obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA
    exact hpos B
  let f : E →ₚ[ℂ] ℂ :=
    { φ.toLinearMap with
      monotone' := by
        intro A B h
        change φ A ≤ φ B
        have h' := hp (B - A) (sub_nonneg.mpr h)
        simpa only [map_sub, sub_nonneg] using h' }
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro A
  obtain ⟨x, hx, hnorm, hA⟩ := CStarAlgebra.exists_sum_four_nonneg A
  conv_lhs => rw [hA, map_sum]
  calc
    ‖∑ i : Fin 4, φ (Complex.I ^ (i : ℕ) • x i)‖ ≤
        ∑ i : Fin 4, ‖φ (Complex.I ^ (i : ℕ) • x i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 4, ‖A‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [map_smul, norm_smul, norm_pow, Complex.norm_I, one_pow, one_mul]
      have hi := PositiveLinearMap.norm_apply_le_of_nonneg f (x i) (hx i)
      change ‖φ (x i)‖ ≤ ‖φ 1‖ * ‖x i‖ at hi
      simpa only [hn, norm_one, one_mul] using hi.trans
        (by simpa only [hn, norm_one, one_mul] using hnorm i)
    _ = 4 * ‖A‖ := by simp

theorem state_norm_bound {d ℓ : ℕ} (ω : State d ℓ) : ‖ω.functional‖ ≤ 4 := by
  let : PartialOrder (QuasiLocal d ℓ) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (QuasiLocal d ℓ) := CStarAlgebra.spectralOrderedRing _
  exact positive_norm_bound ω.functional ω.normalized
    (fun B => ⟨(ω.positive B).2, by simpa using (ω.positive B).1.symm⟩)

open Filter in
theorem bounded_functionals_subsequence {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace.SeparableSpace E]
    (φ : ℕ → E →L[ℂ] ℂ) (C : ℝ) (hb : ∀ n, ‖φ n‖ ≤ C) :
    ∃ ψ : E →L[ℂ] ℂ, ∃ κ : ℕ → ℕ, StrictMono κ ∧
      ∀ A : E, Tendsto (fun n => φ (κ n) A) atTop (nhds (ψ A)) := by
  let u : ℕ → WeakDual ℂ E := fun n => WeakDual.toStrongDual.symm (φ n)
  have hu : ∀ n, u n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 C := by
    intro n
    simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
      u, LinearEquiv.apply_symm_apply] using hb n
  obtain ⟨ψ, _, κ, hκ, hlim⟩ := WeakDual.isSeqCompact_closedBall ℂ E 0 C hu
  exact ⟨WeakDual.toStrongDual ψ, κ, hκ,
    fun A => (WeakDual.eval_continuous A).tendsto ψ |>.comp hlim⟩

open Filter in

theorem state_subsequence {d ℓ : ℕ} (ω : ℕ → State d ℓ) :
    ∃ η : State d ℓ, ∃ κ : ℕ → ℕ, StrictMono κ ∧
      ∀ A : QuasiLocal d ℓ, Tendsto (fun n => (ω (κ n)).functional A)
        atTop (nhds (η.functional A)) := by
  obtain ⟨ψ, κ, hκ, hA⟩ := bounded_functionals_subsequence
    (fun n => (ω n).functional) 4 (fun n => state_norm_bound (ω n))
  have hn : ψ 1 = 1 := by
    have h := hA 1
    simp only [(ω _).normalized] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  have hp (A : QuasiLocal d ℓ) : (ψ (star A * A)).im = 0 ∧ 0 ≤ (ψ (star A * A)).re := by
    constructor
    · have h := Complex.continuous_im.tendsto _ |>.comp (hA (star A * A))
      change Tendsto (fun n => ((ω (κ n)).functional (star A * A)).im) atTop
        (nhds ((ψ (star A * A)).im)) at h
      simp only [((ω _).positive A).1] at h
      exact tendsto_nhds_unique h tendsto_const_nhds
    · exact ge_of_tendsto (Complex.continuous_re.tendsto _ |>.comp (hA (star A * A)))
        (Filter.Eventually.of_forall fun n => ((ω (κ n)).positive A).2)
  exact ⟨⟨ψ, hn, hp⟩, κ, hκ, hA⟩

open scoped InnerProductSpace

theorem finiteTraceFunctional_cyclic_unit {d ℓ : ℕ} (F : Finset (Site d))
    {x : Site d} (hx : x ∈ F) (a b : Level ℓ) (A : QuasiLocal d ℓ) :
    finiteTraceFunctional d ℓ F (localUnit d ℓ x a b * A) =
      finiteTraceFunctional d ℓ F (A * localUnit d ℓ x a b) := by
  simp only [finiteTraceFunctional_apply]
  congr 1
  let e := finiteConfigPerm (⟨x,hx⟩ : F) (Equiv.swap a b)
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro c _
  change (matrixUnit d ℓ x a b) ((A : SpinOperator d ℓ)
      (configVector (extendConfig F (e c)))) (extendConfig F (e c)) =
    (A : SpinOperator d ℓ) ((matrixUnit d ℓ x a b)
      (configVector (extendConfig F c))) (extendConfig F c)
  rw [matrixUnit_apply, matrixUnit_configVector]
  have hext : extendConfig F (e c) = (extendConfig F c).update x
      (Equiv.swap a b (c ⟨x,hx⟩)) := extendConfig_perm _ _ _
  have hcx : extendConfig F c x = c ⟨x,hx⟩ := by simp [hx]
  rw [hext]
  simp only [Finsupp.update_apply, ite_true, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left, hcx]
  by_cases hc : c ⟨x,hx⟩ = b
  · simp only [hc, ite_true, Equiv.swap_apply_right, Finsupp.update_idem]
    rw [← hc, ← hcx, Finsupp.update_self]
  · simp only [hc, ite_false, map_zero, lp.coeFn_zero, Pi.zero_apply]

theorem cyclic_adjoin {E : Type*} [NormedRing E] [NormedAlgebra ℂ E]
    [StarRing E] [StarModule ℂ E] (φ : E →L[ℂ] ℂ) (s : Set E)
    (h : ∀ a ∈ s, (∀ b, φ (a*b) = φ (b*a)) ∧
      (∀ b, φ (star a*b) = φ (b*star a)))
    {a : E} (ha : a ∈ StarAlgebra.adjoin ℂ s) :
    (∀ b, φ (a*b) = φ (b*a)) ∧ (∀ b, φ (star a*b) = φ (b*star a)) := by
  let P : E → Prop := fun a => ∀ b, φ (a*b) = φ (b*a)
  have mulP (a c : E) (ha : P a) (hc : P c) : P (a*c) := by
    intro b
    calc
      φ ((a*c)*b) = φ (a*(c*b)) := by rw [mul_assoc]
      _ = φ ((c*b)*a) := ha _
      _ = φ (c*(b*a)) := by rw [mul_assoc]
      _ = φ ((b*a)*c) := hc _
      _ = φ (b*(a*c)) := by rw [mul_assoc]
  have addP (a c : E) (ha : P a) (hc : P c) : P (a+c) := by
    intro b
    simp only [add_mul, mul_add, map_add, ha b, hc b]
  change P a ∧ P (star a)
  induction ha using StarAlgebra.adjoin_induction with
  | mem a ha => exact h a ha
  | algebraMap z =>
    constructor <;> intro b <;>
      simp [Algebra.algebraMap_eq_smul_one]
  | add a c ha hc iha ihc =>
    exact ⟨addP a c iha.1 ihc.1, by rw [star_add]; exact addP _ _ iha.2 ihc.2⟩
  | mul a c ha hc iha ihc =>
    exact ⟨mulP a c iha.1 ihc.1, by rw [star_mul]; exact mulP _ _ ihc.2 iha.2⟩
  | star a ha iha => exact ⟨iha.2, by simpa only [star_star] using iha.1⟩

theorem cyclic_of_cyclic_units {d ℓ : ℕ} (φ : QuasiLocal d ℓ →L[ℂ] ℂ)
    (h : ∀ x a b A, φ (localUnit d ℓ x a b * A) = φ (A * localUnit d ℓ x a b)) :
    ∀ A B, φ (A*B) = φ (B*A) := by
  intro A B
  have hd : DenseRange ((↑) : localCore d ℓ → QuasiLocal d ℓ) :=
    denseRange_subtype_val.mpr (localCore_dense d ℓ)
  refine hd.induction_on (p := fun C => φ (C*B) = φ (B*C)) A ?_ ?_
  · exact isClosed_eq (φ.continuous.comp (continuous_id.mul continuous_const))
      (φ.continuous.comp (continuous_const.mul continuous_id))
  · intro a
    apply (cyclic_adjoin φ _ ?_ a.property).1
    rintro C ⟨x,a,b,rfl⟩
    exact ⟨h x a b, by simpa only [star_localUnit] using h x b a⟩

theorem exists_tracial_state (d ℓ : ℕ) :
    ∃ τ : State d ℓ, ∀ A B, τ.functional (A*B) = τ.functional (B*A) := by
  obtain ⟨τ,κ,hκ,hlim⟩ := state_subsequence (fun n => finiteTraceState d ℓ (box d n))
  refine ⟨τ, cyclic_of_cyclic_units τ.functional ?_⟩
  intro x a b A
  have he : ∀ᶠ n : ℕ in Filter.atTop,
      (finiteTraceState d ℓ (box d (κ n))).functional (localUnit d ℓ x a b*A) =
      (finiteTraceState d ℓ (box d (κ n))).functional (A*localUnit d ℓ x a b) := by
    filter_upwards [hκ.tendsto_atTop.eventually (eventually_mem_box x)] with n hn
    exact finiteTraceFunctional_cyclic_unit _ hn a b A
  exact tendsto_nhds_unique (hlim _) ((hlim _).congr' (Filter.EventuallyEq.symm he))

end Heisenberg
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_GibbsLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical
open scoped ComplexConjugate BigOperators
open Filter Topology Metric
open scoped NNReal
open scoped ComplexConjugate Topology
open Set Filter Complex
open scoped Topology

namespace Heisenberg

open GibbsStrip

lemma state_apply_norm_le {d ℓ : ℕ} (ω : State d ℓ) (A : QuasiLocal d ℓ) :
    ‖ω.functional A‖ ≤ 4 * ‖A‖ :=
  (ω.functional.le_opNorm A).trans (mul_le_mul_of_nonneg_right (state_norm_bound ω) (norm_nonneg A))

open Filter Topology GibbsStrip

end Heisenberg
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_LatticePaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical

namespace Heisenberg.Geometry

lemma card_boxFinset (d r : ℕ) : (boxFinset d r).card = (2 * r + 1) ^ d := by
  simp only [boxFinset, Fintype.card_piFinset, Int.card_Icc]
  have hc : ((r : ℤ) + 1 + (r : ℤ)).toNat = 2 * r + 1 := by omega
  simp [hc]

end Heisenberg.Geometry
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_CubeSurface
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators
open Filter Topology
namespace Heisenberg
open SpatialFrame
variable {d ℓ : ℕ}

lemma box_card (d n : ℕ) : (box d n).card=(2*n+1)^d := Geometry.card_boxFinset d n
lemma box_mono {n m : ℕ} (hnm : n≤ m) : box d n⊆box d m := by
  intro x hx
  apply (box_mem d m x).mpr
  intro j
  exact (box_mem d n x |>.mp hx j).trans (by exact_mod_cast hnm)

lemma box_ratio_tendsto (d r : ℕ) :
    Tendsto (fun n : ℕ=>((box d n).card:ℝ)/((box d (n+r)).card:ℝ)) atTop (𝓝 1) := by
  have hx : Tendsto (fun n : ℕ=>(2*(n:ℝ)+1)/(2*((n:ℝ)+r)+1)) atTop (𝓝 1) := by
    have hi : Tendsto (fun n : ℕ=>(2*((n:ℝ)+r)+1)⁻¹) atTop (𝓝 0) := by
      apply tendsto_inv_atTop_zero.comp
      exact tendsto_atTop_add_const_right _ 1
        ((tendsto_atTop_add_const_right _ (r:ℝ) tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num : (0:ℝ)<2))
    have hh:=(tendsto_const_nhds (x:=(1:ℝ)) (f:=atTop)).sub (hi.const_mul (2*r:ℝ))
    convert hh using 1
    · ext n
      field_simp
      ring
    · simp
  have hh:=hx.pow d
  simpa only [box_card,Nat.cast_pow,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,div_pow,one_pow] using hh

lemma box_boundary_ratio_tendsto (d r : ℕ) :
    Tendsto (fun n : ℕ=>((box d (n+r)\box d n).card:ℝ)/((box d (n+r)).card:ℝ)) atTop (𝓝 0) := by
  have hh:=(tendsto_const_nhds (x:=(1:ℝ)) (f:=atTop)).sub (box_ratio_tendsto d r)
  convert hh using 1
  · ext n
    rw [Finset.card_sdiff_of_subset (box_mono (Nat.le_add_right n r)),Nat.cast_sub (Finset.card_le_card (box_mono (Nat.le_add_right n r))),sub_div,div_self]
    exact_mod_cast (Finset.card_ne_zero.mpr (box_nonempty d (n+r)))
  · norm_num

end Heisenberg
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SpinAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators ComplexConjugate
open Filter Topology
namespace Heisenberg

variable {d ℓ : ℕ}

lemma averageState_apply {I : Type*} [Fintype I] (μ : I → ℝ) (hμ : ∀ i,0≤μ i)
    (hm : ∑ i,μ i=1) (ω : I → State d ℓ) (A : QuasiLocal d ℓ) :
    (averageState μ hμ hm ω).functional A=∑ i,(μ i:ℂ)*(ω i).functional A := by
  simp only [averageState,sum_apply,smul_apply,smul_eq_mul]

end Heisenberg
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SpinTranslations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace Heisenberg
variable {d ℓ : ℕ}

lemma hom_ext_localUnit (f g : QuasiLocal d ℓ →⋆ₐ[ℂ] QuasiLocal d ℓ)
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x a b,f (localUnit d ℓ x a b)=g (localUnit d ℓ x a b)) : f=g := by
  apply DFunLike.ext
  intro A
  have hs : (localCore d ℓ : Set (QuasiLocal d ℓ))⊆{B | f B=g B} := by
    intro B hB
    exact StarAlgHom.adjoin_le_equalizer f g (by rintro _ ⟨x,a,b,rfl⟩; exact h x a b) hB
  exact (isClosed_eq hf hg).closure_subset_iff.mpr hs ((localCore_dense d ℓ) A)

lemma translation_add (x y : Site d) (A : QuasiLocal d ℓ) :
    translation d ℓ x (translation d ℓ y A)=translation d ℓ (x+y) A := by
  have h : (translation d ℓ x).comp (translation d ℓ y)=translation d ℓ (x+y) := by
    apply hom_ext_localUnit
    · exact (translationLinear d ℓ x).continuous.comp (translationLinear d ℓ y).continuous
    · exact (translationLinear d ℓ (x+y)).continuous
    · intro z a b
      simp only [StarAlgHom.comp_apply,translation_localUnit,add_assoc]
  exact DFunLike.congr_fun h A

end Heisenberg
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SpinBulk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open Filter Topology
namespace Heisenberg
variable {d ℓ : ℕ}

lemma box_add_mem {N r : ℕ} {x y : Site d} (hx : x∈box d N) (hy : y∈box d r) : x+y∈box d (N+r) := by
  apply (box_mem _ _ _).mpr
  intro i
  exact (abs_add_le (x i) (y i)).trans (by
    simpa only [Nat.cast_add] using add_le_add ((box_mem _ _ _).mp hx i) ((box_mem _ _ _).mp hy i))

lemma box_boundary_inner_tendsto (d r : ℕ) :
    Tendsto (fun N : ℕ=>((box d N\box d (N-r)).card:ℝ)/((box d N).card:ℝ)) atTop (𝓝 0) := by
  have hn : Tendsto (fun N : ℕ=>N-r) atTop atTop := by
    refine tendsto_atTop.2 (fun b=>?_)
    filter_upwards [eventually_ge_atTop (b+r)] with N hN
    omega
  apply ((box_boundary_ratio_tendsto d r).comp hn).congr'
  filter_upwards [eventually_ge_atTop r] with N hN
  change ((box d (N-r+r)\box d (N-r)).card:ℝ)/((box d (N-r+r)).card:ℝ)=_
  rw [Nat.sub_add_cancel hN]

lemma image_sdiff_card_le (Λ F : Finset (Site d)) (x : Site d)
    (_hF : F⊆Λ) (hshift : ∀ y∈F,x+y∈Λ) :
    ((Λ.image (fun y=>x+y))\Λ).card≤(Λ\F).card := by
  apply le_trans (Finset.card_le_card (show (Λ.image (fun y=>x+y))\Λ⊆(Λ\F).image (fun y=>x+y) from ?_)) Finset.card_image_le
  intro z hz
  obtain ⟨hz,hzout⟩:=Finset.mem_sdiff.mp hz
  obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hz
  exact Finset.mem_image.mpr ⟨y,Finset.mem_sdiff.mpr ⟨hy,fun hyF=>hzout (hshift y hyF)⟩,rfl⟩

lemma sdiff_image_card (Λ : Finset (Site d)) (x : Site d) :
    (Λ\Λ.image (fun y=>x+y)).card=(Λ.image (fun y=>x+y)\Λ).card := by
  rw [Finset.card_sdiff,Finset.card_sdiff,Finset.card_image_of_injective _ (add_right_injective x),Finset.inter_comm]

end Heisenberg
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_FiniteAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.Average
variable {X E : Type*} [DecidableEq X] [NormedAddCommGroup E]

lemma norm_sum_sub_le (Λ Ξ : Finset X) (f : X → E) (C : ℝ)
    (hf : ∀ x,‖f x‖≤C) :
    ‖∑ x∈Λ,f x-∑ x∈Ξ,f x‖≤((Λ\Ξ).card+(Ξ\Λ).card:ℝ)*C := by
  rw [←Finset.sum_sdiff_sub_sum_sdiff]
  calc _ ≤ ‖∑ x∈Λ\Ξ,f x‖+‖∑ x∈Ξ\Λ,f x‖ := norm_sub_le _ _
       _ ≤ (∑ _∈Λ\Ξ,C)+(∑ _∈Ξ\Λ,C) := add_le_add
         ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun x _=>hf x)))
         ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun x _=>hf x)))
       _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,add_mul]

end Heisenberg.Average
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SpinCubeAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open Filter Topology
namespace Heisenberg
variable {d ℓ : ℕ}

lemma cube_card_pos (d N : ℕ) : (0:ℝ)<(box d N).card := by
  classical
  exact_mod_cast Finset.card_pos.mpr (box_nonempty d N)

lemma cubeAverage_apply (Λ : Finset (Site d)) (hΛ : Λ.Nonempty) (ω : State d ℓ) (A : QuasiLocal d ℓ) :
    (cubeAverage Λ hΛ ω).functional A=(Λ.card:ℂ)⁻¹*∑ x∈Λ,ω.functional (translation d ℓ x A) := by
  classical
  simp only [cubeAverage,averageState_apply,translatedState,ContinuousLinearMap.comp_apply,translationLinear_apply]
  rw [←Finset.mul_sum]
  have hs : (∑ i : Λ,ω.functional (translation d ℓ i.val A))=∑ x∈Λ,ω.functional (translation d ℓ x A) := Finset.sum_coe_sort Λ (fun x=>ω.functional (translation d ℓ x A))
  rw [hs]
  simp only [Complex.ofReal_inv,Complex.ofReal_natCast]

lemma cubeAverage_spinZ (Λ : Finset (Site d)) (hΛ : Λ.Nonempty) (ω : State d ℓ) :
    (cubeAverage Λ hΛ ω).functional (spinZ d ℓ 0)=(Λ.card:ℂ)⁻¹*ω.functional (totalZ Λ) := by
  classical
  rw [cubeAverage_apply]
  simp only [translation_spinZ,add_zero,totalZ,map_sum]

lemma state_selfAdjoint_im (ω : State d ℓ) {A : QuasiLocal d ℓ} (hA : IsSelfAdjoint A) :
    (ω.functional A).im=0 := by
  classical
  have h1:=(ω.positive (A+1)).1
  have h2:=(ω.positive A).1
  simp only [star_add,hA.star_eq,star_one,add_mul,mul_add,mul_one,one_mul,map_add,Complex.add_im,ω.normalized,Complex.one_im] at h1 h2
  linarith

lemma cubeAverage_translation_bound (N r : ℕ) (hr : r≤N) (x : Site d) (hx : x∈box d r)
    (ω : State d ℓ) (A : QuasiLocal d ℓ) :
    ‖(cubeAverage (box d N) (box_nonempty d N) ω).functional (translation d ℓ x A)-
      (cubeAverage (box d N) (box_nonempty d N) ω).functional A‖≤
      (((box d N\box d (N-r)).card:ℝ)/(box d N).card)*(8*‖A‖) := by
  classical
  let Λ:=box d N
  let F:=box d (N-r)
  have hF : F⊆Λ:=box_mono (Nat.sub_le N r)
  have hshift : ∀ y∈F,x+y∈Λ := by
    classical
    intro y hy
    simpa only [Nat.sub_add_cancel hr,add_comm x] using box_add_mem hy hx
  have hbound:=image_sdiff_card_le Λ F x hF hshift
  rw [cubeAverage_apply,cubeAverage_apply,←mul_sub,norm_mul,norm_inv,Complex.norm_natCast]
  have he : (∑ y∈Λ,ω.functional (translation d ℓ y (translation d ℓ x A)))=
      ∑ y∈Λ.image (fun y=>x+y),ω.functional (translation d ℓ y A) := by
    classical
    rw [Finset.sum_image (fun _ _ _ _ he=>add_left_cancel he)]
    apply Finset.sum_congr rfl
    intro y hy
    rw [translation_add,add_comm]
  rw [he]
  have hs:=(Average.norm_sum_sub_le (Λ.image (fun y=>x+y)) Λ
    (fun y=>ω.functional (translation d ℓ y A)) (4*‖A‖) (fun y=>by simpa only [norm_translation] using state_apply_norm_le ω (translation d ℓ y A)))
  have hecard : (((Λ\Λ.image (fun y=>x+y)).card:ℕ):ℝ)=(((Λ.image (fun y=>x+y)\Λ).card:ℕ):ℝ) := by exact_mod_cast sdiff_image_card Λ x
  rw [hecard] at hs
  have hb : ((Λ.image (fun y=>x+y)\Λ).card:ℝ)≤(Λ\F).card := by exact_mod_cast hbound
  have hp : (0:ℝ)<Λ.card:=cube_card_pos d N
  calc _ ≤ (Λ.card:ℝ)⁻¹*((((Λ.image (fun y=>x+y)\Λ).card:ℝ)+((Λ.image (fun y=>x+y)\Λ).card:ℝ))*(4*‖A‖)) := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hp.le)
       _ ≤ (Λ.card:ℝ)⁻¹*(((Λ\F).card+(Λ\F).card:ℝ)*(4*‖A‖)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (add_le_add hb hb) (by positivity)) (inv_nonneg.mpr hp.le)
       _ = _ := by dsimp [Λ,F]; ring

lemma cubeAverage_limit_TI (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (η : ℕ → State d ℓ)
    (ω : State d ℓ) (hω : ∀ A,Tendsto (fun n=>(cubeAverage (box d (N n)) (box_nonempty d (N n)) (η n)).functional A) atTop (𝓝 (ω.functional A))) : TranslationInvariant ω := by
  classical
  intro x A
  obtain ⟨r,hr⟩:=(eventually_mem_box x).exists
  have hlim : Tendsto (fun n=>(cubeAverage (box d (N n)) (box_nonempty d (N n)) (η n)).functional (translation d ℓ x A)-
      (cubeAverage (box d (N n)) (box_nonempty d (N n)) (η n)).functional A) atTop (𝓝 0) := by
    classical
    apply squeeze_zero_norm' (a:=fun n=>(((box d (N n)\box d (N n-r)).card:ℝ)/(box d (N n)).card)*(8*‖A‖))
    · filter_upwards [hN.eventually (eventually_ge_atTop r)] with n hn
      exact cubeAverage_translation_bound (N n) r hn x hr (η n) A
    · simpa only [Function.comp_def,zero_mul] using ((box_boundary_inner_tendsto d r).comp hN).mul_const (8*‖A‖)
  exact sub_eq_zero.mp (tendsto_nhds_unique ((hω _).sub (hω A)) hlim)

end Heisenberg
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open Filter Topology
namespace Heisenberg

lemma complex_nat_inv_mul_re (n : ℕ) (z : ℂ) :
    ((n : ℂ)⁻¹ * z).re = z.re / (n : ℝ) := by
  have hc : (n : ℂ)⁻¹ = Complex.ofReal ((n : ℝ)⁻¹) := by
    simp only [Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [hc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

lemma cubeAverage_order {d ℓ : ℕ} (Λ : Finset (Site d)) (hΛ : Λ.Nonempty)
    (ω : State d ℓ) (hmag : (Λ.card : ℝ) * ℓ / 8 ≤ (ω.functional (totalZ Λ)).re) :
    (ℓ : ℝ) / 8 ≤ ((cubeAverage Λ hΛ ω).functional (spinZ d ℓ 0)).re := by
  have hr := congrArg Complex.re (cubeAverage_spinZ Λ hΛ ω)
  rw [complex_nat_inv_mul_re] at hr
  rw [hr]
  have hp : 0 < (Λ.card : ℝ) := by exact_mod_cast hΛ.card_pos
  exact (le_div_iff₀ hp).mpr (by nlinarith)

theorem ordered_state_exists (d ℓ : ℕ) (hd : 2≤d) [NeZero ℓ] :
    ∃ β₀ : ℝ,0<β₀ ∧ ∀ β : ℝ,β₀≤β →
      ∃ ω : State (d+1) ℓ,TranslationInvariant ω ∧ IsKMS β ω ∧
        (ω.functional (spinZ (d+1) ℓ 0)).im=0 ∧
        (ℓ:ℝ)/8≤(ω.functional (spinZ (d+1) ℓ 0)).re := by
  obtain ⟨τ,hτ⟩:=exists_tracial_state (d+1) ℓ
  obtain ⟨β₀,hβ₀,horder⟩:=Selection.field_ordered_cubes d ℓ hd τ hτ
  refine ⟨β₀,hβ₀,?_⟩
  intro β hβ
  let h : ℕ → ℝ:=fun n=>(n+1:ℝ)⁻¹
  have hhpos (n : ℕ) : 0<h n := by dsimp [h]; positivity
  have hh : Tendsto h atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hex (n : ℕ) : ∃ m : ℕ,n ≤ m ∧
      ((box (d+1) (m+1)).card:ℝ)*ℓ/8≤
        ((gibbsState τ (shiftedField (box (d+1) (m+1)) (h n)) β).functional (totalZ (box (d+1) (m+1)))).re := by
    exact ((eventually_ge_atTop n).and (horder β hβ (h n) (hhpos n))).exists
  choose m hm hmag using hex
  let N : ℕ → ℕ:=fun n=>m n+1
  have hN : Tendsto N atTop atTop := tendsto_atTop_mono (fun n=>by exact (hm n).trans (Nat.le_succ _)) tendsto_id
  let η : ℕ → State (d+1) ℓ:=fun n=>gibbsState τ (shiftedField (box (d+1) (N n)) (h n)) β
  let ρ : ℕ → State (d+1) ℓ:=fun n=>cubeAverage (box (d+1) (N n)) (box_nonempty (d+1) (N n)) (η n)
  have hρ (n : ℕ) : (ℓ:ℝ)/8≤((ρ n).functional (spinZ (d+1) ℓ 0)).re :=
    cubeAverage_order _ _ (η n) (hmag n)
  obtain ⟨ω,κ,hκ,hω⟩:=state_subsequence ρ
  refine ⟨ω,?_,?_,?_,?_⟩
  · exact cubeAverage_limit_TI (N∘κ) (hN.comp hκ.tendsto_atTop) (η∘κ) ω hω
  · exact cubeAverage_limit_KMS τ hτ (lt_of_lt_of_le hβ₀ hβ) (N∘κ) (hN.comp hκ.tendsto_atTop)
      (h∘κ) (hh.comp hκ.tendsto_atTop) ω hω
  · exact state_selfAdjoint_im ω (star_spinZ (d+1) ℓ 0)
  · exact ge_of_tendsto (Complex.continuous_re.tendsto _ |>.comp (hω (spinZ (d+1) ℓ 0)))
      (Filter.Eventually.of_forall (fun n=>hρ (κ n)))

theorem spontaneous_magnetization_oai (d ℓ : ℕ) (hd : 3≤d) (hℓ : 1≤ℓ) :
    DynamicsConverges d ℓ ∧
      ∃ β₀ : ℝ,0<β₀ ∧ ∀ β : ℝ,β₀≤β →
        ∃ ω : State d ℓ,TranslationInvariant ω ∧ IsKMS β ω ∧
          (ω.functional (spinZ d ℓ 0)).im=0 ∧
          (ℓ:ℝ)/8≤(ω.functional (spinZ d ℓ 0)).re := by
  have : NeZero ℓ:=⟨by omega⟩
  refine ⟨dynamics_converges d ℓ,?_⟩
  obtain ⟨k,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : d≠0)
  exact ordered_state_exists k ℓ (by omega)

end Heisenberg
end
end

end OAI
end

theorem solution : type_of% @OAI.Heisenberg.spontaneous_magnetization_oai := @OAI.Heisenberg.spontaneous_magnetization_oai

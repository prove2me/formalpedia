-- Prove2me | solution 1 for OAI.Heisenberg.cubeAverage_limit_KMS
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T08:46:46.437951+00:00
-- url     : https://prove2.me/submissions/3473e277-f00a-4941-a452-b369107d3483

import Mathlib
import Definitions.Def_Heisenberg
import Definitions.Def_OAIW2HM002
import Theorems.Thm_OAI_Heisenberg_cubeBoundary_error
import Theorems.Thm_OAI_Heisenberg_field_local_small
import Theorems.Thm_OAI_Heisenberg_finiteDynamics_deep_uniform
import Theorems.Thm_OAI_Heisenberg_finite_cube_gibbs_strip
import Theorems.Thm_OAI_Heisenberg_state_limit_locallyUniform

section
-- module Solutions.OAIW2_Heis.Heisenberg_LocalAlgebra
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

lemma localUnit_mem_localAlgebra (d ℓ : ℕ) (F : Set (Site d)) {x : Site d}
    (hx : x ∈ F) (a b : Level ℓ) : localUnit d ℓ x a b ∈ localAlgebra d ℓ F :=
  StarAlgebra.subset_adjoin ℂ _ ⟨x, hx, a, b, rfl⟩

lemma spinZ_mem_localAlgebra (d ℓ : ℕ) (F : Set (Site d)) {x : Site d} (hx : x ∈ F) :
    spinZ d ℓ x ∈ localAlgebra d ℓ F := by
  apply Subalgebra.sum_mem
  intro k _
  exact (localAlgebra d ℓ F).smul_mem (localUnit_mem_localAlgebra d ℓ F hx k k) _

lemma spinPlus_mem_localAlgebra (d ℓ : ℕ) (F : Set (Site d)) {x : Site d} (hx : x ∈ F) :
    spinPlus d ℓ x ∈ localAlgebra d ℓ F := by
  apply Subalgebra.sum_mem
  intro k _
  exact (localAlgebra d ℓ F).smul_mem (localUnit_mem_localAlgebra d ℓ F hx k.succ k.castSucc) _

lemma spinMinus_mem_localAlgebra (d ℓ : ℕ) (F : Set (Site d)) {x : Site d} (hx : x ∈ F) :
    spinMinus d ℓ x ∈ localAlgebra d ℓ F :=
  star_mem (spinPlus_mem_localAlgebra d ℓ F hx)

lemma spinX_mem_localAlgebra (d ℓ : ℕ) (F : Set (Site d)) {x : Site d} (hx : x ∈ F) :
    spinX d ℓ x ∈ localAlgebra d ℓ F :=
  (localAlgebra d ℓ F).smul_mem ((localAlgebra d ℓ F).add_mem
    (spinPlus_mem_localAlgebra d ℓ F hx) (spinMinus_mem_localAlgebra d ℓ F hx)) _

lemma spinY_mem_localAlgebra (d ℓ : ℕ) (F : Set (Site d)) {x : Site d} (hx : x ∈ F) :
    spinY d ℓ x ∈ localAlgebra d ℓ F :=
  (localAlgebra d ℓ F).smul_mem ((localAlgebra d ℓ F).sub_mem
    (spinPlus_mem_localAlgebra d ℓ F hx) (spinMinus_mem_localAlgebra d ℓ F hx)) _

theorem localAlgebras_commute {d ℓ : ℕ} {F G : Set (Site d)} (hFG : Disjoint F G)
    {A B : QuasiLocal d ℓ} (hA : A ∈ localAlgebra d ℓ F) (hB : B ∈ localAlgebra d ℓ G) :
    Commute A B := by
  have hg (x : Site d) (hx : x ∈ F) (a b : Level ℓ) :
      localAlgebra d ℓ G ≤ StarSubalgebra.centralizer ℂ {localUnit d ℓ x a b} := by
    apply StarAlgebra.adjoin_le
    rintro _ ⟨y, hy, c, e, rfl⟩
    have hxy : x ≠ y := fun h => (Set.disjoint_left.mp hFG hx) (h ▸ hy)
    change _ ∈ StarSubalgebra.centralizer ℂ _
    rw [StarSubalgebra.mem_centralizer_iff ℂ]
    rintro _ rfl
    exact ⟨(localUnits_commute hxy a b c e).eq, by
      rw [star_localUnit]
      exact (localUnits_commute hxy b a c e).eq⟩
  have hle : localAlgebra d ℓ F ≤ StarSubalgebra.centralizer ℂ {B} := by
    apply StarAlgebra.adjoin_le
    rintro _ ⟨x, hx, a, b, rfl⟩
    have h₁ := ((StarSubalgebra.mem_centralizer_iff ℂ).mp (hg x hx a b hB)) _ (Set.mem_singleton _)
    have h₂ := ((StarSubalgebra.mem_centralizer_iff ℂ).mp
      (hg x hx a b (star_mem hB))) _ (Set.mem_singleton _)
    change _ ∈ StarSubalgebra.centralizer ℂ _
    rw [StarSubalgebra.mem_centralizer_iff ℂ]
    rintro _ rfl
    exact ⟨h₁.1.symm, h₂.1.symm⟩
  exact (((StarSubalgebra.mem_centralizer_iff ℂ).mp (hle hA)) B (Set.mem_singleton B)).1.symm

lemma singleton_local_commute {d ℓ : ℕ} {x y : Site d} (hxy : x ≠ y)
    {A B : QuasiLocal d ℓ} (hA : A ∈ localAlgebra d ℓ {x})
    (hB : B ∈ localAlgebra d ℓ {y}) : Commute A B :=
  localAlgebras_commute (Set.disjoint_singleton.mpr hxy) hA hB

lemma nearestNeighbor_ne {d : ℕ} {x y : Site d} (h : NearestNeighbor x y) : x ≠ y := by
  intro he
  subst y
  simp [NearestNeighbor] at h

theorem star_hamiltonian (d ℓ : ℕ) (Λ : Finset (Site d)) :
    star (hamiltonian d ℓ Λ) = hamiltonian d ℓ Λ := by
  classical
  simp only [hamiltonian, star_neg, star_sum, star_add, star_mul,
    star_spinX, star_spinY, star_spinZ]
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  have hxy := nearestNeighbor_ne (Finset.mem_filter.mp he).2.1
  have hX := singleton_local_commute hxy (spinX_mem_localAlgebra d ℓ {e.1} rfl)
    (spinX_mem_localAlgebra d ℓ {e.2} rfl)
  have hY := singleton_local_commute hxy (spinY_mem_localAlgebra d ℓ {e.1} rfl)
    (spinY_mem_localAlgebra d ℓ {e.2} rfl)
  have hZ := singleton_local_commute hxy (spinZ_mem_localAlgebra d ℓ {e.1} rfl)
    (spinZ_mem_localAlgebra d ℓ {e.2} rfl)
  rw [hX.eq, hY.eq, hZ.eq]

lemma imaginaryTime_skew (t : ℝ) : Complex.I * (t : ℂ) ∈ skewAdjoint ℂ := by
  change star (Complex.I * (t : ℂ)) = -(Complex.I * (t : ℂ))
  simp

lemma hamiltonian_selfAdjoint (d ℓ : ℕ) (Λ : Finset (Site d)) :
    IsSelfAdjoint (hamiltonian d ℓ Λ) := star_hamiltonian d ℓ Λ

lemma timeHamiltonian_skew (d ℓ : ℕ) (Λ : Finset (Site d)) (t : ℝ) :
    (Complex.I * (t : ℂ)) • hamiltonian d ℓ Λ ∈ skewAdjoint (QuasiLocal d ℓ) :=
  IsSelfAdjoint.smul_mem_skewAdjoint (imaginaryTime_skew t) (hamiltonian_selfAdjoint d ℓ Λ)

lemma finiteUnitary (d ℓ : ℕ) (Λ : Finset (Site d)) (t : ℝ) :
    NormedSpace.exp ((Complex.I * (t : ℂ)) • hamiltonian d ℓ Λ) ∈ unitary (QuasiLocal d ℓ) :=
  NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (timeHamiltonian_skew d ℓ Λ t)

lemma finiteInverseUnitary (d ℓ : ℕ) (Λ : Finset (Site d)) (t : ℝ) :
    NormedSpace.exp ((-(Complex.I * (t : ℂ))) • hamiltonian d ℓ Λ) ∈ unitary (QuasiLocal d ℓ) := by
  convert finiteUnitary d ℓ Λ (-t) using 1; simp

theorem norm_finiteDynamics (d ℓ : ℕ) (Λ : Finset (Site d)) (t : ℝ) (A : QuasiLocal d ℓ) :
    ‖finiteDynamics d ℓ Λ t A‖ = ‖A‖ := by
  rw [finiteDynamics, CStarRing.norm_mul_mem_unitary _ (finiteInverseUnitary d ℓ Λ t),
    CStarRing.norm_mem_unitary_mul _ (finiteUnitary d ℓ Λ t)]

lemma finiteDynamics_sub (d ℓ : ℕ) (Λ : Finset (Site d)) (t : ℝ) (A B : QuasiLocal d ℓ) :
    finiteDynamics d ℓ Λ t (A - B) = finiteDynamics d ℓ Λ t A - finiteDynamics d ℓ Λ t B := by
  simp [finiteDynamics, mul_sub, sub_mul]

theorem finiteDynamics_isometry (d ℓ : ℕ) (Λ : Finset (Site d)) (t : ℝ) :
    Isometry (finiteDynamics d ℓ Λ t) := by
  apply Isometry.of_dist_eq
  intro A B
  simp only [dist_eq_norm, ← finiteDynamics_sub, norm_finiteDynamics]

lemma localAlgebra_mono {d ℓ : ℕ} {F G : Set (Site d)} (h : F ⊆ G) :
    localAlgebra d ℓ F ≤ localAlgebra d ℓ G := by
  apply StarAlgebra.adjoin_mono
  rintro A ⟨x, hx, a, b, rfl⟩
  exact ⟨x, h hx, a, b, rfl⟩

end Heisenberg
end

end OAI
end

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

lemma eventually_subset_box {d : ℕ} (F : Finset (Site d)) :
    ∀ᶠ n : ℕ in Filter.atTop, F ⊆ box d n := by
  have h : ∀ x : F, ∀ᶠ n : ℕ in Filter.atTop, (x : Site d) ∈ box d n :=
    fun x => eventually_mem_box (x : Site d)
  filter_upwards [Filter.eventually_all.mpr h] with n hn
  intro x hx
  exact hn ⟨x,hx⟩

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

lemma localCore_finite_support {d ℓ : ℕ} {A : QuasiLocal d ℓ}
    (hA : A ∈ localCore d ℓ) : ∃ F : Finset (Site d), A ∈ localAlgebra d ℓ (F : Set (Site d)) := by
  induction hA using StarAlgebra.adjoin_induction with
  | mem a ha =>
    obtain ⟨x,a,b,rfl⟩ := ha
    exact ⟨{x},localUnit_mem_localAlgebra _ _ _ (by simp) _ _⟩
  | algebraMap z => exact ⟨∅, by simpa only [Finset.coe_empty] using
      (localAlgebra d ℓ ∅).algebraMap_mem z⟩
  | add a b ha hb iha ihb =>
    obtain ⟨F,hF⟩ := iha
    obtain ⟨G,hG⟩ := ihb
    refine ⟨F ∪ G,(localAlgebra d ℓ (↑(F ∪ G) : Set (Site d))).add_mem ?_ ?_⟩
    · exact localAlgebra_mono (by intro x hx; exact Finset.mem_union_left _ hx) hF
    · exact localAlgebra_mono (by intro x hx; exact Finset.mem_union_right _ hx) hG
  | mul a b ha hb iha ihb =>
    obtain ⟨F,hF⟩ := iha
    obtain ⟨G,hG⟩ := ihb
    refine ⟨F ∪ G,(localAlgebra d ℓ (↑(F ∪ G) : Set (Site d))).mul_mem ?_ ?_⟩
    · exact localAlgebra_mono (by intro x hx; exact Finset.mem_union_left _ hx) hF
    · exact localAlgebra_mono (by intro x hx; exact Finset.mem_union_right _ hx) hG
  | star a ha iha =>
    obtain ⟨F,hF⟩ := iha
    exact ⟨F,star_mem hF⟩

end Heisenberg

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_BoundedStrip
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

open scoped ComplexConjugate Topology
namespace GibbsStrip
variable {E : Type*} [CStarAlgebra E]

attribute [local instance] OAI.GibbsStrip.instNormedAlgebraRat_solutions
lemma real_evolve_norm {K : E} (hK : IsSelfAdjoint K) (t : ℝ) (A : E) :
    ‖evolve K (t : ℂ) A‖ = ‖A‖ := by
  have h (t : ℝ) : NormedSpace.exp ((Complex.I*(t:ℂ)) • K) ∈ unitary E := by
    apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    apply IsSelfAdjoint.smul_mem_skewAdjoint _ hK
    change star (Complex.I*(t:ℂ)) = -(Complex.I*(t:ℂ))
    simp
  have hn : NormedSpace.exp ((-(Complex.I*(t:ℂ))) • K) ∈ unitary E := by
    convert h (-t) using 1; simp
  rw [evolve,CStarRing.norm_mul_mem_unitary _ hn,CStarRing.norm_mem_unitary_mul _ (h t)]

end GibbsStrip

open Set Filter Complex
open scoped Topology

namespace HeisenbergStrip

theorem closure_openStrip {β : ℝ} (hβ : 0 < β) :
    closure (openStrip β) = closedStrip β := by
  simp only [openStrip, closedStrip, Complex.closure_preimage_im, closure_Ioo hβ.ne]

theorem isOpen_openStrip (β : ℝ) : IsOpen (openStrip β) :=
  isOpen_Ioo.preimage Complex.continuous_im

theorem bounded_strip_max {β C : ℝ} (hβ : 0 < β) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (openStrip β))
    (hbounded : ∃ M : ℝ, ∀ z ∈ closedStrip β, ‖f z‖ ≤ M)
    (hzero : ∀ z : ℂ, z.im = 0 → ‖f z‖ ≤ C)
    (htop : ∀ z : ℂ, z.im = β → ‖f z‖ ≤ C)
    {z : ℂ} (hz : z ∈ closedStrip β) : ‖f z‖ ≤ C := by
  apply PhragmenLindelof.horizontal_strip hf ?_ hzero htop hz.1 hz.2
  refine ⟨0, by simpa using div_pos Real.pi_pos hβ, 0, ?_⟩
  obtain ⟨M, hM⟩ := hbounded
  apply Asymptotics.IsBigO.of_bound M
  simp only [Filter.eventually_inf_principal]
  exact Filter.Eventually.of_forall (fun w hw => by
    simpa using hM w ⟨hw.1.le, hw.2.le⟩)

theorem gaussian_differentiable : Differentiable ℂ gaussian :=
  Complex.differentiable_exp.comp (differentiable_id.mul differentiable_id).neg

theorem norm_gaussian (z : ℂ) : ‖gaussian z‖ = Real.exp (-z.re ^ 2 + z.im ^ 2) := by
  rw [gaussian, Complex.norm_exp]
  congr 1
  simp only [Complex.neg_re, Complex.mul_re]
  ring

theorem norm_gaussian_le {β : ℝ} {z : ℂ} (hz : z ∈ closedStrip β) :
    ‖gaussian z‖ ≤ Real.exp (β ^ 2) := by
  rw [norm_gaussian]
  apply Real.exp_le_exp.mpr
  have := sq_le_sq₀ hz.1 (hz.1.trans hz.2)
  nlinarith [sq_nonneg z.re, this.mpr hz.2]

theorem norm_gaussian_tail {β R : ℝ} (hR : 0 ≤ R) {z : ℂ}
    (hz : z ∈ closedStrip β) (hreal : R ≤ |z.re|) :
    ‖gaussian z‖ ≤ Real.exp (-(R ^ 2) + β ^ 2) := by
  rw [norm_gaussian]
  apply Real.exp_le_exp.mpr
  have hi := (sq_le_sq₀ hz.1 (hz.1.trans hz.2)).mpr hz.2
  have hr := (sq_le_sq₀ hR (abs_nonneg z.re)).mpr hreal
  rw [sq_abs] at hr
  linarith

theorem boundary_mem_closedStrip {β : ℝ} (hβ : 0 ≤ β) {z : ℂ}
    (hz : z.im = 0 ∨ z.im = β) : z ∈ closedStrip β := by
  rcases hz with hz | hz <;> exact ⟨by linarith, by linarith⟩

theorem gaussian_uniformCauchy {β C : ℝ} (hβ : 0 < β) (_hC : 0 ≤ C)
    {F : ℕ → ℂ → ℂ} (hd : ∀ n, DiffContOnCl ℂ (F n) (openStrip β))
    (hbound : ∀ n z, z ∈ closedStrip β → ‖F n z‖ ≤ C)
    (hcauchy : BoundaryCauchy β F) :
    UniformCauchySeqOn (fun n z => gaussian z * F n z) atTop (closedStrip β) := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have ht : Tendsto (fun R : ℝ => Real.exp (-(R ^ 2) + β ^ 2) * (2 * C))
      atTop (𝓝 0) := by
    have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0))).mul_const
        (Real.exp (β ^ 2))
    simpa only [Real.exp_add, zero_mul, mul_assoc, Function.comp_apply] using h.mul_const (2 * C)
  obtain ⟨R, hR, htail⟩ := ((Filter.eventually_ge_atTop (1 : ℝ)).and
    (ht.eventually_lt_const (by linarith : 0 < ε / 2))).exists
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have he : 0 < Real.exp (β ^ 2) := Real.exp_pos _
  obtain ⟨N, hN⟩ := hcauchy R hRpos (ε / (2 * Real.exp (β ^ 2)))
    (div_pos hε (mul_pos (by norm_num) he))
  refine ⟨N, ?_⟩
  intro m hm n hn z hz
  have hdiff (w : ℂ) (hw : w ∈ closedStrip β) : ‖F m w - F n w‖ ≤ 2 * C :=
    (norm_sub_le _ _).trans (by linarith [hbound m w hw, hbound n w hw])
  have hboundDiff : ∃ M : ℝ, ∀ w ∈ closedStrip β,
      ‖gaussian w * F m w - gaussian w * F n w‖ ≤ M := by
    refine ⟨Real.exp (β ^ 2) * (2 * C), ?_⟩
    intro w hw
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (norm_gaussian_le hw) (hdiff w hw) (norm_nonneg _) he.le
  have hedge (w : ℂ) (hw : w.im = 0 ∨ w.im = β) :
      ‖gaussian w * F m w - gaussian w * F n w‖ ≤ ε / 2 := by
    have hwS := boundary_mem_closedStrip hβ.le hw
    rw [← mul_sub, norm_mul]
    by_cases hwr : |w.re| ≤ R
    · apply le_of_lt
      calc
        ‖gaussian w‖ * ‖F m w - F n w‖ ≤
            Real.exp (β ^ 2) * ‖F m w - F n w‖ :=
          mul_le_mul_of_nonneg_right (norm_gaussian_le hwS) (norm_nonneg _)
        _ < Real.exp (β ^ 2) * (ε / (2 * Real.exp (β ^ 2))) :=
          mul_lt_mul_of_pos_left (hN m hm n hn w hw hwr) he
        _ = ε / 2 := by field_simp
    · exact (mul_le_mul (norm_gaussian_tail hRpos.le hwS (not_le.mp hwr).le)
        (hdiff w hwS) (norm_nonneg _) (Real.exp_pos _).le).trans htail.le
  have hmax := bounded_strip_max hβ
    ((gaussian_differentiable.diffContOnCl.smul (hd m)).sub
      (gaussian_differentiable.diffContOnCl.smul (hd n))) hboundDiff
    (fun w hw => hedge w (Or.inl hw)) (fun w hw => hedge w (Or.inr hw)) hz
  rw [dist_eq_norm]
  exact hmax.trans_lt (by linarith)

theorem strip_limit_of_boundaryCauchy {β C : ℝ} (hβ : 0 < β) (hC : 0 ≤ C)
    {F : ℕ → ℂ → ℂ} (hd : ∀ n, DiffContOnCl ℂ (F n) (openStrip β))
    (hbound : ∀ n z, z ∈ closedStrip β → ‖F n z‖ ≤ C)
    (hcauchy : BoundaryCauchy β F) :
    ∃ f : ℂ → ℂ, TendstoLocallyUniformlyOn F f atTop (closedStrip β) ∧
      DiffContOnCl ℂ f (openStrip β) ∧ ∀ z ∈ closedStrip β, ‖f z‖ ≤ C := by
  classical
  have hgC := gaussian_uniformCauchy hβ hC hd hbound hcauchy
  have hex (z : ℂ) : ∃ w : ℂ, z ∈ closedStrip β →
      Tendsto (fun n => gaussian z * F n z) atTop (𝓝 w) := by
    by_cases hz : z ∈ closedStrip β
    · obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete (hgC.cauchySeq hz)
      exact ⟨w, fun _ => hw⟩
    · exact ⟨0, fun h => (hz h).elim⟩
  choose g hg using hex
  have hgu : TendstoUniformlyOn (fun n z => gaussian z * F n z) g atTop
      (closedStrip β) := hgC.tendstoUniformlyOn_of_tendsto hg
  have hgc : ContinuousOn g (closedStrip β) := by
    apply hgu.continuousOn
    apply Filter.Eventually.frequently
    apply Filter.Eventually.of_forall
    intro n
    exact gaussian_differentiable.continuous.continuousOn.mul
      (by simpa only [closure_openStrip hβ] using (hd n).continuousOn)
  let inverseGaussian : ℂ → ℂ := fun z => Complex.exp (z * z)
  have hic : Continuous inverseGaussian :=
    Complex.continuous_exp.comp (continuous_id.mul continuous_id)
  have hiu : TendstoUniformlyOn (fun _ : ℕ => inverseGaussian)
      inverseGaussian atTop (closedStrip β) := by
    rw [Metric.tendstoUniformlyOn_iff]
    exact fun ε hε => Filter.Eventually.of_forall (fun _ _ _ => by simpa)
  have hloc := hiu.tendstoLocallyUniformlyOn.mul₀ hgu.tendstoLocallyUniformlyOn
    hic.continuousOn hgc
  have hFi (n : ℕ) (z : ℂ) :
      inverseGaussian z * (gaussian z * F n z) = F n z := by
    dsimp only [inverseGaussian, gaussian]
    rw [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
  have hlocF : TendstoLocallyUniformlyOn F (fun z => inverseGaussian z * g z)
      atTop (closedStrip β) := hloc.congr (fun n z _ => hFi n z)
  refine ⟨fun z => inverseGaussian z * g z, hlocF, ⟨?_, ?_⟩, ?_⟩
  · exact (hlocF.mono (fun _ hz => ⟨hz.1.le, hz.2.le⟩)).differentiableOn
      (Filter.Eventually.of_forall (fun n => (hd n).differentiableOn))
      (isOpen_openStrip β)
  · rw [closure_openStrip hβ]
    exact hic.continuousOn.mul hgc
  · intro z hz
    exact le_of_tendsto ((hlocF.tendsto_at hz).norm)
      (Filter.Eventually.of_forall (fun n => hbound n z hz))

theorem boundaryCauchy_of_locallyUniform {β : ℝ} {F : ℕ → ℂ → ℂ}
    {f₀ fβ : ℝ → ℂ}
    (h₀ : TendstoLocallyUniformly (fun n (t : ℝ) => F n (t : ℂ)) f₀ atTop)
    (hβ : TendstoLocallyUniformly (fun n (t : ℝ) => F n ((t : ℂ) + Complex.I * β))
      fβ atTop) : BoundaryCauchy β F := by
  intro R _ ε hε
  have hu₀ := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
    (isCompact_Icc : IsCompact (Icc (-R) R))).mp h₀.tendstoLocallyUniformlyOn
  have huβ := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
    (isCompact_Icc : IsCompact (Icc (-R) R))).mp hβ.tendstoLocallyUniformlyOn
  obtain ⟨N₀, hN₀⟩ := Metric.uniformCauchySeqOn_iff.mp hu₀.uniformCauchySeqOn ε hε
  obtain ⟨Nβ, hNβ⟩ := Metric.uniformCauchySeqOn_iff.mp huβ.uniformCauchySeqOn ε hε
  refine ⟨max N₀ Nβ, ?_⟩
  intro m hm n hn z hz hr
  have hr' : z.re ∈ Icc (-R) R := abs_le.mp hr
  rcases hz with hz | hz
  · have heq : (z.re : ℂ) = z := by
      apply Complex.ext <;> simp [hz]
    simpa only [heq, dist_eq_norm] using
      hN₀ m ((le_max_left _ _).trans hm) n ((le_max_left _ _).trans hn) z.re hr'
  · have heq : (z.re : ℂ) + Complex.I * β = z := by
      apply Complex.ext <;> simp [hz]
    simpa only [heq, dist_eq_norm] using
      hNβ m ((le_max_right _ _).trans hm) n ((le_max_right _ _).trans hn) z.re hr'

theorem bounded_strip_limit {β C : ℝ} (hβ : 0 < β) (hC : 0 ≤ C)
    {F : ℕ → ℂ → ℂ} {f₀ fβ : ℝ → ℂ}
    (hd : ∀ n, DiffContOnCl ℂ (F n) (openStrip β))
    (hbounded : ∀ n, ∃ M : ℝ, ∀ z ∈ closedStrip β, ‖F n z‖ ≤ M)
    (hzero : ∀ n (t : ℝ), ‖F n (t : ℂ)‖ ≤ C)
    (htop : ∀ n (t : ℝ), ‖F n ((t : ℂ) + Complex.I * β)‖ ≤ C)
    (hconv₀ : TendstoLocallyUniformly (fun n (t : ℝ) => F n (t : ℂ)) f₀ atTop)
    (hconvβ : TendstoLocallyUniformly
      (fun n (t : ℝ) => F n ((t : ℂ) + Complex.I * β)) fβ atTop) :
    ∃ f : ℂ → ℂ, TendstoLocallyUniformlyOn F f atTop (closedStrip β) ∧
      DiffContOnCl ℂ f (openStrip β) ∧
      (∀ z ∈ closedStrip β, ‖f z‖ ≤ C) ∧
      (∀ t : ℝ, f (t : ℂ) = f₀ t) ∧
      (∀ t : ℝ, f ((t : ℂ) + Complex.I * β) = fβ t) := by
  have hb (n : ℕ) (z : ℂ) (hz : z ∈ closedStrip β) : ‖F n z‖ ≤ C := by
    apply bounded_strip_max hβ (hd n) (hbounded n) ?_ ?_ hz
    · intro w hw
      have heq : (w.re : ℂ) = w := by apply Complex.ext <;> simp [hw]
      simpa only [heq] using hzero n w.re
    · intro w hw
      have heq : (w.re : ℂ) + Complex.I * β = w := by
        apply Complex.ext <;> simp [hw]
      simpa only [heq] using htop n w.re
  obtain ⟨f, hf, hfd, hfb⟩ := strip_limit_of_boundaryCauchy hβ hC hd hb
    (boundaryCauchy_of_locallyUniform hconv₀ hconvβ)
  refine ⟨f, hf, hfd, hfb, ?_, ?_⟩
  · intro t
    have ht : (t : ℂ) ∈ closedStrip β := by
      constructor <;> simp [hβ.le]
    exact tendsto_nhds_unique (hf.tendsto_at ht) (hconv₀.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ t))
  · intro t
    have ht : (t : ℂ) + Complex.I * β ∈ closedStrip β := by
      constructor <;> simp [hβ.le]
    exact tendsto_nhds_unique (hf.tendsto_at ht) (hconvβ.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ t))

end HeisenbergStrip
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
-- module Solutions.OAIW2_Heis.Heisenberg_SpinField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix Matrix.Norms.Operator
namespace Heisenberg
open SlotTensor TensorMatrix
variable {d ℓ : ℕ}

lemma totalZ_selfAdjoint (Λ : Finset (Site d)) : IsSelfAdjoint (totalZ (ℓ:=ℓ) Λ) := by
  change star (totalZ Λ)=totalZ Λ
  simp only [totalZ,star_sum,star_spinZ]

lemma shiftedField_selfAdjoint (Λ : Finset (Site d)) (h : ℝ) :
    IsSelfAdjoint (shiftedField (ℓ:=ℓ) Λ h) := by
  change star (shiftedField Λ h)=shiftedField Λ h
  simp only [shiftedField,star_sub,star_add,star_smul,star_trivial,star_one,
    (hamiltonian_selfAdjoint d ℓ Λ).star_eq,(totalZ_selfAdjoint (ℓ:=ℓ) Λ).star_eq]

end Heisenberg
end
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
-- module Solutions.OAIW2_Heis.Heisenberg_SpinFieldDynamics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate
open Filter Topology
namespace GibbsStrip
variable {E : Type*} [CStarAlgebra E]

lemma evolve_sub (K A B : E) (z : ℂ) : evolve K z (A-B)=evolve K z A-evolve K z B := by
  simp only [evolve,mul_sub,sub_mul]

lemma real_evolve_dist (K : E) (hK : IsSelfAdjoint K) (t : ℝ) (A B : E) :
    dist (evolve K t A) (evolve K t B)=dist A B := by
  rw [dist_eq_norm,←evolve_sub,real_evolve_norm hK,dist_eq_norm]

end GibbsStrip
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

end Heisenberg
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SpinFieldUniform
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
lemma metric_triangle5 {E : Type*} [PseudoMetricSpace E] (a b c d e : E) :
    dist a e≤dist a b+dist b c+dist c d+dist d e :=
  (dist_triangle a d e).trans (add_le_add (dist_triangle4 a b c d) le_rfl)
variable {d ℓ : ℕ}

theorem field_deep_uniform (A : QuasiLocal d ℓ) (K : Set ℝ) (hK : IsCompact K)
    {ε : ℝ} (hε : 0<ε) : ∃ r : ℕ,∃ δ : ℝ,0<δ ∧
      ∀ Γ : Finset (Site d),box d r⊆Γ → ∀ h : ℝ,|h|<δ → ∀ t∈K,
        dist (GibbsStrip.evolve (shiftedField Γ h) t A) (dynamics d ℓ t A)<ε := by
  obtain ⟨B,hB,hAB⟩:=(localCore_dense d ℓ).exists_dist_lt A (show 0<ε/8 by positivity)
  obtain ⟨F,hF⟩:=localCore_finite_support hB
  obtain ⟨r₀,hr₀⟩:=(eventually_subset_box F).exists
  obtain ⟨r₁,hr₁⟩:=finiteDynamics_deep_uniform d ℓ A K hK (show 0<ε/4 by positivity)
  obtain ⟨δ,hδ,hfield⟩:=field_local_small F B hF K hK (show 0<ε/4 by positivity)
  refine ⟨max r₀ r₁,δ,hδ,?_⟩
  intro Γ hΓ h hh t ht
  have hFΓ : F⊆Γ :=hr₀.trans ((box_mono (le_max_left r₀ r₁)).trans hΓ)
  have hdeep : box d r₁⊆Γ :=(box_mono (le_max_right r₀ r₁)).trans hΓ
  calc _ ≤ dist (GibbsStrip.evolve (shiftedField Γ h) t A) (GibbsStrip.evolve (shiftedField Γ h) t B)+
      dist (GibbsStrip.evolve (shiftedField Γ h) t B) (finiteDynamics d ℓ Γ t B)+
      dist (finiteDynamics d ℓ Γ t B) (finiteDynamics d ℓ Γ t A)+
      dist (finiteDynamics d ℓ Γ t A) (dynamics d ℓ t A) := metric_triangle5 _ _ _ _ _
       _ = dist A B+dist (GibbsStrip.evolve (shiftedField Γ h) t B) (finiteDynamics d ℓ Γ t B)+dist B A+
         dist (finiteDynamics d ℓ Γ t A) (dynamics d ℓ t A) := by
           rw [GibbsStrip.real_evolve_dist _ (shiftedField_selfAdjoint Γ h), (finiteDynamics_isometry d ℓ Γ t).dist_eq]
       _ < ε := by have h1:=hfield Γ hFΓ h hh t ht; have h2:=hr₁ Γ hdeep t ht; rw [dist_comm B A]; linarith

end Heisenberg
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SpinAverageBoundary
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

lemma scaled_quarter {ε C : ℝ} (hε : 0<ε) (hC : 0≤C) :
    C*(ε/(4*(C+1)))<ε/4 := by
  have hp : 0<C+1:=by linarith
  apply (lt_div_iff₀ (by norm_num : (0:ℝ)<4)).mpr
  field_simp
  nlinarith

theorem cubeBoundary_locallyUniform (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0)) (η : ℕ → State d ℓ)
    (ω : State d ℓ) (hω : ∀ A,Tendsto (fun n=>(cubeAverage (box d (N n)) (box_nonempty d (N n)) (η n)).functional A) atTop (𝓝 (ω.functional A)))
    (M : QuasiLocal d ℓ →L[ℂ] QuasiLocal d ℓ) (B : QuasiLocal d ℓ) :
    TendstoLocallyUniformly (fun n t=>cubeBoundary (box d (N n)) (η n) (h n) M B t)
      (fun t=>ω.functional (M (dynamics d ℓ t B))) atTop := by
  classical
  apply tendstoLocallyUniformly_iff_forall_isCompact.mpr
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨r,δ,hδ,hgood⟩:=field_deep_uniform B K hK (show 0<ε/(4*(4*‖M‖+1)) by positivity)
  have hsmall := (Metric.tendsto_nhds.mp hh) δ hδ
  have hratio : Tendsto (fun n=>(((box d (N n)\box d (N n-r)).card:ℝ)/(box d (N n)).card)*(8*‖M‖*‖B‖)) atTop (𝓝 0) := by
    classical
    simpa only [Function.comp_def,zero_mul] using ((box_boundary_inner_tendsto d r).comp hN).mul_const (8*‖M‖*‖B‖)
  have heval := tendstoLocallyUniformly_iff_forall_isCompact.mp (state_limit_locallyUniform hω M B) K hK
  filter_upwards [hN.eventually (eventually_ge_atTop r),hsmall,
    hratio.eventually (eventually_lt_nhds (show (0:ℝ)<ε/4 by positivity)),
    (Metric.tendstoUniformlyOn_iff.mp heval) (ε/4) (by positivity)] with n hn hhn hb he
  intro t ht
  have hhn' : |h n|<δ := by simpa only [dist_zero_right,Real.norm_eq_abs] using hhn
  have herr:=cubeBoundary_error (N n) r hn (η n) (h n) t M B (show 0≤ε/(4*(4*‖M‖+1)) by positivity)
    (fun Γ hΓ=>(hgood Γ hΓ (h n) hhn' t ht).le)
  have hpart:=scaled_quarter hε (show 0≤4*‖M‖ by positivity)
  have htri:=dist_triangle (ω.functional (M (dynamics d ℓ t B)))
    ((cubeAverage (box d (N n)) (box_nonempty d (N n)) (η n)).functional (M (dynamics d ℓ t B)))
    (cubeBoundary (box d (N n)) (η n) (h n) M B t)
  rw [←dist_eq_norm,dist_comm] at herr
  have hei:=he t ht
  linarith

end Heisenberg
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SpinAveragedKMS
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

theorem cubeAverage_limit_KMS_oai (τ : State d ℓ)
    (hτ : ∀ A B,τ.functional (A*B)=τ.functional (B*A))
    {β : ℝ} (hβ : 0<β) (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0)) (ω : State d ℓ)
    (hω : ∀ A,Tendsto (fun n=>(cubeAverage (box d (N n)) (box_nonempty d (N n))
      (gibbsState τ (shiftedField (box d (N n)) (h n)) β)).functional A) atTop (𝓝 (ω.functional A))) : IsKMS β ω := by
  refine ⟨hβ,fun A B=>?_⟩
  choose F hd hb hzero htop using fun n=>finite_cube_gibbs_strip (box d (N n)) (box_nonempty d (N n)) (h n) τ hτ hβ A B
  let η : ℕ → State d ℓ:=fun n=>gibbsState τ (shiftedField (box d (N n)) (h n)) β
  have hl:=cubeBoundary_locallyUniform N hN h hh η ω hω (ContinuousLinearMap.mul ℂ (QuasiLocal d ℓ) A) B
  have hu:=cubeBoundary_locallyUniform N hN h hh η ω hω ((ContinuousLinearMap.mul ℂ (QuasiLocal d ℓ)).flip A) B
  have hf0 : TendstoLocallyUniformly (fun n (t : ℝ)=>F n t) (fun t=>ω.functional (A*dynamics d ℓ t B)) atTop := by
    simpa only [hzero,ContinuousLinearMap.mul_apply',η] using hl
  have hf1 : TendstoLocallyUniformly (fun n (t : ℝ)=>F n ((t:ℂ)+Complex.I*β)) (fun t=>ω.functional (dynamics d ℓ t B*A)) atTop := by
    simpa only [htop,ContinuousLinearMap.flip_apply,ContinuousLinearMap.mul_apply',η] using hu
  obtain ⟨f,_,hfd,hfb,hfzero,hftop⟩:=HeisenbergStrip.bounded_strip_limit hβ
    (show 0≤4*‖A‖*‖B‖ by positivity) hd (fun n=>⟨4*‖A‖*‖B‖,hb n⟩)
    (fun n t=>hb n t (by constructor <;> simp [hβ.le]))
    (fun n t=>hb n ((t:ℂ)+Complex.I*β) (by constructor <;> simp [hβ.le])) hf0 hf1
  refine ⟨f,?_,hfd.1,⟨4*‖A‖*‖B‖,fun z hz0 hz1=>hfb z ⟨hz0,hz1⟩⟩,hfzero,hftop⟩
  simpa only [HeisenbergStrip.closure_openStrip hβ, HeisenbergStrip.closedStrip, Set.preimage, Set.mem_Icc] using hfd.2

end Heisenberg
end
end

end OAI
end

theorem solution : type_of% @OAI.Heisenberg.cubeAverage_limit_KMS_oai := @OAI.Heisenberg.cubeAverage_limit_KMS_oai

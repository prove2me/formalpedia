-- Prove2me | solution 1 for GlobalTheory.Mass.SemiBasis.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:05:09.959624+00:00
-- url     : https://prove2.me/submissions/37781328-7baa-44d7-b415-de30f4ceb362

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemLocDIffSpan
import Theorems.Thm_GlobalTheory_Mass_SemiBasis_mem_A
import Theorems.Thm_GlobalTheory_Mass_SemiBasis_alg_ne_zero
import Theorems.Thm_GlobalTheory_Mass_SemiBasis_isPID
import Theorems.Thm_GlobalTheory_Mass_SemiBasis_mem_locD_iff_span
import Theorems.Thm_GlobalTheory_Mass_SemiBasis_mem_locD_one
import Theorems.Thm_GlobalTheory_Mass_SemiBasis_isLattice_span
import Theorems.Thm_GlobalTheory_Mass_SemiBasis_mem_iff_repr
import Theorems.Thm_GlobalTheory_Mass_SemiBasis_relIndex_of_repr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.SemiBasis
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.Mass.SemiBasis
theorem _root_.solution : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M M' : Submodule (𝓞 K) V) (d : ℕ), 2 ≤ d → Submodule.IsLattice K M → Submodule.IsLattice K M' → M ≤ M' → ∃ (b : Module.Basis (Fin (Module.finrank K V)) K V) (a : Fin (Module.finrank K V) → 𝓞 K), (∀ i, a i ≠ 0) ∧ (∀ x, x ∈ locD (d : 𝓞 K) M' ↔ ∀ i, b.repr x i ∈ locD (d : 𝓞 K) (1 : Submodule (𝓞 K) K)) ∧ (∀ x, x ∈ locD (d : 𝓞 K) M ↔ ∀ i, b.repr x i ∈ scl (a i) (locD (d : 𝓞 K) (1 : Submodule (𝓞 K) K))) ∧ idxN (locD (d : 𝓞 K) M') (locD (d : 𝓞 K) M) = ∏ i, idxN (locD (d : 𝓞 K) (1 : Submodule (𝓞 K) K)) (scl (a i) (locD (d : 𝓞 K) (1 : Submodule (𝓞 K) K))) := by
  intro K V _ _ _ _ _ _ _ M M' d hd hM hM' hle
  have := isPID (K := K) hd
  set N := Submodule.span (A K hd) (M : Set V) with hN
  set N' := Submodule.span (A K hd) (M' : Set V) with hN'
  have lN : Submodule.IsLattice K N := isLattice_span hd M hM
  have lN' : Submodule.IsLattice K N' := isLattice_span hd M' hM'
  have hNle : N ≤ N' := Submodule.span_mono hle
  have r : Module.finrank (A K hd) N = Module.finrank K V := by
    unfold Module.finrank; rw [Submodule.IsLattice.rank' K N]
  have r' : Module.finrank (A K hd) N' = Module.finrank K V := by
    unfold Module.finrank; rw [Submodule.IsLattice.rank' K N']
  have : Module.Free (A K hd) N' := Submodule.IsLattice.free K N'
  let e := Submodule.comapSubtypeEquivOfLe hNle
  obtain ⟨c', α, c, hc⟩ := Submodule.exists_smith_normal_form_of_rank_eq
    (N := N.comap N'.subtype) (Module.finBasisOfFinrankEq (A K hd) N' r')
    (by rw [e.finrank_eq, r, r'])
  choose a s hs has using fun i => (mem_A hd (α i : K)).1 (α i).2
  set b := c'.extendOfIsLattice K with hb
  set b₀ := (c.map e).extendOfIsLattice K with hb₀
  have hbb : ∀ i, b₀ i = (α i : K) • b i := by
    intro i
    have := congrArg Subtype.val (hc i)
    rw [hb₀, hb, Module.Basis.extendOfIsLattice_apply, Module.Basis.extendOfIsLattice_apply]
    exact this
  have hα : ∀ i, (α i : K) ≠ 0 := by
    intro i h0
    apply b₀.ne_zero i
    rw [hbb, h0, zero_smul]
  have ha : ∀ i, a i ≠ 0 := by
    intro i h0
    apply hα i
    rw [has, h0]; simp
  have hrep : ∀ x i, b.repr x i = (α i : K) * b₀.repr x i := by
    intro x i
    conv_lhs => rw [← b₀.sum_repr x]
    simp [hbb, smul_smul, Finsupp.single_apply, mul_comm]
  have h1 : ∀ x, x ∈ locD (d : 𝓞 K) M' ↔
      ∀ i, b.repr x i ∈ locD (d : 𝓞 K) (1 : Submodule (𝓞 K) K) := by
    intro x
    rw [mem_locD_iff_span hd, ← hN', mem_iff_repr hd N' c']
    simp only [mem_locD_one hd, hb]
  have h2 : ∀ x, x ∈ locD (d : 𝓞 K) M ↔
      ∀ i, b.repr x i ∈ scl (a i) (locD (d : 𝓞 K) (1 : Submodule (𝓞 K) K)) := by
    intro x
    rw [mem_locD_iff_span hd, ← hN, mem_iff_repr hd N (c.map e)]
    refine forall_congr' fun i => ?_
    rw [← hb₀, hrep, has]
    have hs0 := alg_ne_zero hd (hs i)
    have ha0 : algebraMap (𝓞 K) K (a i) ≠ 0 := by simpa using ha i
    simp only [scl, Submodule.mem_map, LinearMap.lsmul_apply, mem_locD_one hd, Algebra.smul_def]
    constructor
    · intro h
      refine ⟨(algebraMap (𝓞 K) K (s i))⁻¹ * b₀.repr x i,
        mul_mem ((mem_A hd _).mpr ⟨1, s i, hs i, by simp⟩) h, by ring⟩
    · rintro ⟨y, hy, hy'⟩
      have : b₀.repr x i = algebraMap (𝓞 K) K (s i) * y := by
        field_simp at hy' ⊢
        linear_combination -hy'
      rw [this]
      exact mul_mem (Subalgebra.algebraMap_mem _ _) hy
  exact ⟨b, a, ha, h1, h2, relIndex_of_repr b _ _ _ _ h1 h2⟩
end GlobalTheory.Mass.SemiBasis

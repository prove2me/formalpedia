-- Prove2me | solution 1 for OAI.Lech.TensorConductor.length_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:03:30.553339+00:00
-- url     : https://prove2.me/submissions/bc4576c0-7895-49dc-bf52-7ee860cf5507

import Mathlib
import Definitions.Def_OAIQ032L016

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PerfectDomainStagesTensorTo
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors


namespace Lech.NormalizedLength.Tower
variable {L : Type*} [CommRing L] (T : Tower L)
variable {M N P : Type*} [AddCommGroup M] [Module L M]
  [AddCommGroup N] [Module L N] [AddCommGroup P] [Module L P]

 

lemma length_kernel_eq_cokernel (f : M →ₗ[L] M) (hM : T.length M ≠ ⊤) :
    T.length f.ker = T.length (M ⧸ f.range) := by
  have h₁ := T.length_eq_add_of_exact f.rangeRestrict.ker.subtype f.rangeRestrict
    (Submodule.subtype_injective _) f.surjective_rangeRestrict
    (LinearMap.exact_subtype_ker_map f.rangeRestrict)
  have hk : f.rangeRestrict.ker = f.ker := by ext x; simp
  rw [hk] at h₁
  have h₂ := T.length_eq_add_of_exact f.range.subtype f.range.mkQ
    (Submodule.subtype_injective _) f.range.mkQ_surjective
    (LinearMap.exact_subtype_mkQ f.range)
  have hr : T.length f.range ≠ ⊤ :=
    ne_top_of_le_ne_top hM (T.length_le_of_injective f.range.subtype
      (Submodule.subtype_injective _))
  exact (ENNReal.add_right_inj hr).mp ((add_comm _ _).trans (h₁.symm.trans h₂))

 

lemma length_torsion_subquotient_le (i : N →ₗ[L] M) (q : N →ₗ[L] P)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (g : L) (hg : ∀ x : P, g • x = 0) (hM : T.length M ≠ ⊤) :
    T.length P ≤ T.length (M ⧸ (LinearMap.lsmul L M g).range) := by
  let fN := LinearMap.lsmul L N g
  let fM := LinearMap.lsmul L M g
  have hqker : fN.range ≤ q.ker := by
    rintro x ⟨y,rfl⟩
    change q (g • y) = 0
    rw [map_smul,hg]
  let q' := fN.range.liftQ q hqker
  have hq' : Function.Surjective q' := by
    intro x
    obtain ⟨y,rfl⟩ := hq x
    exact ⟨fN.range.mkQ y,rfl⟩
  let i' : fN.ker →ₗ[L] fM.ker :=
    (i.comp fN.ker.subtype).codRestrict fM.ker (by
      intro x
      change g • i x = 0
      rw [← map_smul]
      simpa only [fN, LinearMap.lsmul_apply, map_zero] using congrArg i x.property)
  have hi' : Function.Injective i' := by
    intro x y h
    apply Subtype.ext
    apply hi
    exact congrArg Subtype.val h
  have hN : T.length N ≠ ⊤ :=
    ne_top_of_le_ne_top hM (T.length_le_of_injective i hi)
  calc
    T.length P ≤ T.length (N ⧸ fN.range) :=
      T.length_le_of_surjective q' hq'
    _ = T.length fN.ker := (T.length_kernel_eq_cokernel fN hN).symm
    _ ≤ T.length fM.ker := T.length_le_of_injective i' hi'
    _ = _ := T.length_kernel_eq_cokernel fM hM
end Lech.NormalizedLength.Tower


namespace Lech.NormalizedLength.Tower
open Filter
open scoped Topology
variable {L : Type*} [CommRing L] (T : Tower L)
  (M : ℕ → Type*) [∀ n, AddCommGroup (M n)] [∀ n, Module L (M n)]
  {N : Type*} [AddCommGroup N] [Module L N]

 

theorem length_stage_tendsto (f : ∀ n, M n →ₗ[L] N)
    (hm : Monotone (fun n => (f n).range))
    (hex : ∀ x : N, ∃ n, x ∈ (f n).range)
    (e : ℕ → ℝ≥0∞) (he : Tendsto e atTop (𝓝 0))
    (hker : ∀ n, T.length (f n).ker ≤ e n) :
    Tendsto (fun n => T.length (M n)) atTop (𝓝 (T.length N)) := by
  have hmono : Monotone (fun n => T.length (f n).range) := by
    intro n m hnm
    exact T.length_le_of_injective (Submodule.inclusion (hm hnm))
      (Submodule.inclusion_injective (hm hnm))
  have hr : Tendsto (fun n => T.length (f n).range) atTop (𝓝 (T.length N)) := by
    rw [T.length_eq_iSup_of_directed _ hm.directed_le hex]
    exact tendsto_atTop_iSup hmono
  have hup := he.add hr
  rw [zero_add] at hup
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hr hup
  · intro n
    exact T.length_range_le (f n)
  · intro n
    have h := T.length_eq_kernel_add (f n).rangeRestrict (f n).surjective_rangeRestrict
    have hk : (f n).rangeRestrict.ker = (f n).ker := by ext x; simp
    rw [hk] at h
    change T.length (M n) ≤ e n + T.length (f n).range
    rw [h]
    exact add_le_add (hker n) le_rfl

end Lech.NormalizedLength.Tower


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TensorConductor
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal
namespace Lech.TensorConductor

section Conductor
variable {D R C : Type*} [CommRing D] [CommRing R] [CommRing C]
  [Algebra R C] [Algebra D C]
  (B : Subalgebra R C) (hf : ∀ d : D, algebraMap D C d ∈ B)

variable [Algebra D B] [IsScalarTower D B C]

variable (M : Type*) [AddCommGroup M] [Module D M]

lemma conductor_composition (g : R) (hg : ∀ c : C, g • c ∈ B) :
    (conductor (D := D) B M g hg).comp (inclusion (D := D) B M) = g • (LinearMap.id : B ⊗[D] M →ₗ[R] B ⊗[D] M) := by
  apply LinearMap.ext
  intro t
  induction t using OAI.tensorInductionOn with
  | tmul b m => rfl
  | add x y hx hy => simpa only [map_add, LinearMap.add_apply] using congrArg₂ (·+·) hx hy

lemma kernel_killed (g : R) (hg : ∀ c : C, g • c ∈ B)
    (x : (inclusion (D := D) B M).ker) : g • x = 0 := by
  apply Subtype.ext
  have h := LinearMap.congr_fun (conductor_composition (D := D) B M g hg) x
  change conductor (D := D) B M g hg (inclusion (D := D) B M x) = g • (x : B ⊗[D] M) at h
  rw [x.property, map_zero] at h
  exact h.symm
end Conductor
section Stages
variable {D R C : Type*} [CommRing D] [CommRing R] [CommRing C]
  [Algebra R C] [Algebra D C]
  (B : ℕ → Subalgebra R C) [∀ n, Algebra D (B n)]
  [∀ n, IsScalarTower D (B n) C]
  (M : Type*) [AddCommGroup M] [Module D M]

lemma ranges_mono (hm : Monotone B) :
    Monotone (fun n => (inclusion (D := D) (B n) M).range) := by
  intro n m hnm y hy
  obtain ⟨t,rfl⟩ := hy
  induction t using OAI.tensorInductionOn with
  | tmul b x => exact ⟨(⟨b,hm hnm b.property⟩ : B m) ⊗ₜ[D] x,rfl⟩
  | add t u ht hu =>
    simpa only [map_add] using (inclusion (D := D) (B m) M).range.add_mem ht hu

lemma ranges_exhaustive (hm : Monotone B) (hex : ∀ c : C, ∃ n, c ∈ B n) :
    ∀ x : C ⊗[D] M, ∃ n, x ∈ (inclusion (D := D) (B n) M).range := by
  intro x
  induction x using OAI.tensorInductionOn with
  | tmul c x =>
    obtain ⟨n,hn⟩ := hex c
    exact ⟨n,⟨c,hn⟩ ⊗ₜ[D] x,rfl⟩
  | add x y hx hy =>
    obtain ⟨n,hn⟩ := hx
    obtain ⟨m,hm'⟩ := hy
    exact ⟨max n m,(inclusion (D := D) (B (max n m)) M).range.add_mem
      (ranges_mono (D := D) B M hm (le_max_left _ _) hn)
      (ranges_mono (D := D) B M hm (le_max_right _ _) hm')⟩

open Filter
open scoped Topology
 

theorem length_tendsto_oai (T : NormalizedLength.Tower R)
    (hm : Monotone B) (hex : ∀ c : C, ∃ n, c ∈ B n)
    (g : ℕ → R) (hg : ∀ n c, g n • c ∈ B n)
    (hfinite : ∀ n, T.length ((B n) ⊗[D] M) ≠ ⊤)
    (herr : Tendsto (fun n => T.length (((B n) ⊗[D] M) ⧸
      (LinearMap.lsmul R ((B n) ⊗[D] M) (g n)).range)) atTop (𝓝 0)) :
    Tendsto (fun n => T.length ((B n) ⊗[D] M)) atTop
      (𝓝 (T.length (C ⊗[D] M))) := by
  apply T.length_stage_tendsto (fun n => (B n) ⊗[D] M)
    (fun n => inclusion (D := D) (B n) M) (ranges_mono (D := D) B M hm)
    (ranges_exhaustive (D := D) B M hm hex) _ herr
  intro n
  let F := inclusion (D := D) (B n) M
  have hs : Function.Surjective (LinearMap.id : F.ker →ₗ[R] F.ker) := fun x => ⟨x,rfl⟩
  exact T.length_torsion_subquotient_le (M := (B n) ⊗[D] M) (N := F.ker) (P := F.ker)
    F.ker.subtype (LinearMap.id : F.ker →ₗ[R] F.ker) (Submodule.subtype_injective _) hs
    (g n) (kernel_killed (D := D) (B n) M (g n) (hg n)) (hfinite n)
end Stages
end Lech.TensorConductor

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Lech.TensorConductor.length_tendsto_oai.{u_1, u_2, u_3, u_4} := @OAI.Lech.TensorConductor.length_tendsto_oai.{u_1, u_2, u_3, u_4}

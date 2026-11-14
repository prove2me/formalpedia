-- Prove2me | solution 1 for LatticePrepro.CodeFamily.codeDist_extend
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:28:01.463191+00:00
-- url     : https://prove2.me/submissions/5602fca1-6126-471c-b946-c37768256eba

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes

namespace LatticePrepro end LatticePrepro

namespace LatticePrepro

namespace CodeFamily

variable {F : Type} [Field F] {X : Type}

lemma codeDist_le [DecidableEq F] {M : Type} [Fintype M] (y : M → F) (C : Submodule F (M → F))
    {c : M → F} (hc : c ∈ C) : codeDist y C ≤ hammingDist y c :=
  Nat.sInf_le ⟨c, hc, rfl⟩

lemma exists_codeDist_eq [DecidableEq F] {M : Type} [Fintype M] (y : M → F)
    (C : Submodule F (M → F)) : ∃ c ∈ C, hammingDist y c = codeDist y C := by
  have hne : {d | ∃ c ∈ C, hammingDist y c = d}.Nonempty := ⟨hammingDist y 0, 0, C.zero_mem, rfl⟩
  exact Nat.sInf_mem hne

end CodeFamily

section Extend

variable {p : ℕ} [Fact p.Prime] {X : Type} (F : Type) [Field F] [Algebra (ZMod p) F]

/-- Coordinatewise extension of scalars along `algebraMap`. -/
def CodeFamily.liftWord {M : Type} (c : M → ZMod p) : M → F := fun i => algebraMap (ZMod p) F (c i)

lemma CodeFamily.liftWord_mem_extend (C : CodeFamily (ZMod p) X) {c : C.M → ZMod p}
    (hc : c ∈ C.code) : CodeFamily.liftWord F c ∈ (C.extend F).code := by
  show CodeFamily.liftWord F c ∈ Submodule.span F
    ((fun c : C.M → ZMod p => fun i => algebraMap (ZMod p) F (c i)) '' C.code)
  exact Submodule.subset_span ⟨c, hc, rfl⟩

lemma CodeFamily.hammingDist_liftWord [DecidableEq F] {M : Type} [Fintype M] (y c : M → ZMod p) :
    hammingDist (CodeFamily.liftWord F y) (CodeFamily.liftWord F c) = hammingDist y c :=
  hammingDist_comp (fun _ => algebraMap (ZMod p) F) fun _ => (algebraMap (ZMod p) F).injective

/-- An `𝔽_p`-linear retraction `ρ : F → 𝔽_p` with `ρ ∘ algebraMap = id`. -/
lemma CodeFamily.exists_retraction (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) F] :
    ∃ ρ : F →ₗ[ZMod p] ZMod p, ∀ a : ZMod p, ρ (algebraMap (ZMod p) F a) = a := by
  obtain ⟨ρ, hρ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap (ZMod p) F)
    (LinearMap.ker_eq_bot.mpr (algebraMap (ZMod p) F).injective)
  exact ⟨ρ, fun a => by simpa using LinearMap.congr_fun hρ a⟩

/-- Every word of the extended code retracts to a word of the original code. -/
lemma CodeFamily.exists_retract_mem (C : CodeFamily (ZMod p) X) (ρ : F →ₗ[ZMod p] ZMod p)
    {c : C.M → F} (hc : c ∈ (C.extend F).code) :
    ∃ c' ∈ C.code, ∀ i, ρ (c i) = c' i := by
  simp only [CodeFamily.extend] at hc
  obtain ⟨n, a, g, hsum⟩ := Submodule.mem_span_set'.mp hc
  choose w hw using fun j : Fin n => (g j).2
  refine ⟨∑ j, ρ (a j) • w j, Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hw j).1,
    fun i => ?_⟩
  rw [← hsum]
  simp only [Finset.sum_apply, Pi.smul_apply, map_sum, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← (hw j).2]
  show ρ (a j * algebraMap (ZMod p) F (w j i)) = ρ (a j) * w j i
  rw [mul_comm (a j), ← Algebra.smul_def, map_smul, smul_eq_mul]
  ring

/-- Extending scalars preserves the distance from a target over `𝔽_p` to the code
(proof of Lemma 3.11). -/
private theorem CodeFamily.codeDist_extend [DecidableEq F] (C : CodeFamily (ZMod p) X) (x : X) :
    CodeFamily.codeDist ((C.extend F).target x) (C.extend F).code =
      CodeFamily.codeDist (C.target x) C.code := by
  have htarget : (C.extend F).target x = CodeFamily.liftWord F (C.target x) := rfl
  apply le_antisymm
  · obtain ⟨c, hc, hd⟩ := CodeFamily.exists_codeDist_eq (C.target x) C.code
    rw [← hd, htarget, ← CodeFamily.hammingDist_liftWord F]
    exact CodeFamily.codeDist_le _ _ (C.liftWord_mem_extend F hc)
  · obtain ⟨ρ, hρ⟩ := CodeFamily.exists_retraction F p
    obtain ⟨c, hc, hd⟩ := CodeFamily.exists_codeDist_eq ((C.extend F).target x) (C.extend F).code
    obtain ⟨c', hc', hcc'⟩ := C.exists_retract_mem F ρ hc
    rw [← hd]
    calc CodeFamily.codeDist (C.target x) C.code ≤ hammingDist (C.target x) c' :=
          CodeFamily.codeDist_le _ _ hc'
      _ = hammingDist (fun i => ρ ((C.extend F).target x i)) (fun i => ρ (c i)) := by
          congr 1
          · funext i; exact (hρ _).symm
          · funext i; exact (hcc' i).symm
      _ ≤ hammingDist ((C.extend F).target x) c := hammingDist_comp_le_hammingDist fun _ => ρ

end Extend

end LatticePrepro

open LatticePrepro
variable {p : ℕ} [Fact p.Prime] {X : Type} (F : Type) [Field F] [Algebra (ZMod p) F]
theorem solution [DecidableEq F] (C : CodeFamily (ZMod p) X) (x : X) :
    CodeFamily.codeDist ((C.extend F).target x) (C.extend F).code =
      CodeFamily.codeDist (C.target x) C.code :=
  @LatticePrepro.CodeFamily.codeDist_extend p _ X F _ _ _ C x

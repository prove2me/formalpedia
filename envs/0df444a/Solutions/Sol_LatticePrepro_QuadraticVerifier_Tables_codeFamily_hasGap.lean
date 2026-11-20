-- Prove2me | solution 1 for LatticePrepro.QuadraticVerifier.Tables.codeFamily_hasGap
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-20T00:22:10.092184+00:00
-- url     : https://prove2.me/submissions/e8bf4555-2499-467c-87f9-e1643b19ec34

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_Codes_Ext
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_ConstructionA_Ext
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Hadamard_Ext
import Definitions.Def_LatticePrepro_Conversions_Padding
import Definitions.Def_LatticePrepro_Conversions_Lattices
import Definitions.Def_LatticePrepro_Conversions_Lattices_Ext
import Definitions.Def_LatticePrepro_Lattices_Distance
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Reduction_FixedSystem
import Definitions.Def_LatticePrepro_Tables_Digits
import Definitions.Def_LatticePrepro_Tables_FieldSetup
import Definitions.Def_LatticePrepro_Tables_Hankel
import Definitions.Def_LatticePrepro_Tables_Construction
import Definitions.Def_LatticePrepro_Tables_ElementTable
import Definitions.Def_LatticePrepro_Tables_TableSoundness
import Definitions.Def_LatticePrepro_Tables_Explicit
import Definitions.Def_LatticePrepro_Lattices_Mathlib
import Definitions.Def_LatticePrepro_Main
import Definitions.Def_LatticePrepro_Verifier_Gates
import Definitions.Def_LatticePrepro_Verifier_Circuit
import Definitions.Def_LatticePrepro_Verifier_Expr
import Definitions.Def_LatticePrepro_Verifier_ThreeSAT
import Definitions.Def_LatticePrepro_ThreeSAT
import Definitions.Def_LatticePrepro_ThreeSAT_Ext
import Definitions.Def_LatticePrepro_Explicit
import Theorems.Thm_LatticePrepro_CodeFamily_codeDist_extend
import Theorems.Thm_LatticePrepro_LinearSystemFamily_code_no
import Theorems.Thm_LatticePrepro_LinearSystemFamily_code_yes
import Theorems.Thm_LatticePrepro_QuadraticVerifier_Tables_system_spec
import Theorems.Thm_LatticePrepro_params_spec

namespace LatticePrepro end LatticePrepro
namespace LatticePrepro.QuadraticVerifier end LatticePrepro.QuadraticVerifier
namespace LatticePrepro.QuadraticVerifier.Tables end LatticePrepro.QuadraticVerifier.Tables

namespace LatticePrepro

namespace LinearSystemFamily

variable {F : Type} [Field F] {X : Type}

variable (L : LinearSystemFamily F X)

/-- Number of columns `n = D · b`. -/
lemma card_ι : Fintype.card L.ι = L.numBlocks * L.blockSize := by
  classical
  rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := L.blk) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  simp [L.card_fiber, Finset.sum_const, numBlocks]

end LinearSystemFamily

end LatticePrepro

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

lemma lt_codeDist_of_forall [DecidableEq F] {M : Type} [Fintype M] (y : M → F)
    (C : Submodule F (M → F)) {d : ℕ} (h : ∀ c ∈ C, d < hammingDist y c) : d < codeDist y C := by
  obtain ⟨c, hc, hd⟩ := exists_codeDist_eq y C
  rw [← hd]; exact h c hc

end CodeFamily

section OfSystem

variable {p : ℕ} [Fact p.Prime] {X : Type} (L : LinearSystemFamily (ZMod p) X)

theorem LinearSystemFamily.codeDist_le_of_yes {x : X} (hx : L.IsYes x) :
    CodeFamily.codeDist (L.codeTarget x) L.code ≤ L.numBlocks := by
  obtain ⟨e, _, _, he, hmem⟩ := L.code_yes hx
  calc CodeFamily.codeDist (L.codeTarget x) L.code ≤ hammingDist (L.codeTarget x) (L.codeTarget x - e) :=
        CodeFamily.codeDist_le _ _ hmem
    _ = hammingNorm e := by
        rw [hammingDist_comm, hammingDist_eq_hammingNorm]
        congr 1
        abel
    _ ≤ L.numBlocks := he

theorem LinearSystemFamily.lt_codeDist_of_no {g : ℕ} (hg : g < L.blockSize)
    (hD : 0 < L.numBlocks) {x : X} (hx : L.IsNo g x) :
    g * L.numBlocks < CodeFamily.codeDist (L.codeTarget x) L.code :=
  CodeFamily.lt_codeDist_of_forall _ _ (L.code_no hg hD hx)

end OfSystem

end LatticePrepro

namespace LatticePrepro

/-- From the parameter choice: `16 · M^δ ≤ g` whenever `M ≤ 4 n` and `64 n^δ ≤ g`. -/
lemma rpow_le_of_le_four_mul {M n : ℕ} {g δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hM : M ≤ 4 * n)
    (h64 : 64 * (n : ℝ) ^ δ ≤ g) : 16 * (M : ℝ) ^ δ ≤ g := by
  have hMR : (M : ℝ) ≤ 4 * n := by exact_mod_cast hM
  calc 16 * (M : ℝ) ^ δ ≤ 16 * (4 * (n : ℝ)) ^ δ := by gcongr
    _ = 16 * (4 : ℝ) ^ δ * (n : ℝ) ^ δ := by rw [Real.mul_rpow (by norm_num) (by positivity)]; ring
    _ ≤ 16 * 4 * (n : ℝ) ^ δ := by
        gcongr
        calc (4 : ℝ) ^ δ ≤ (4 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hδ1
          _ = 4 := Real.rpow_one 4
    _ = 64 * (n : ℝ) ^ δ := by ring
    _ ≤ g := h64

end LatticePrepro

namespace LatticePrepro

namespace LinearSystemFamily

variable {p : ℕ} [Fact p.Prime] {X : Type} (L : LinearSystemFamily (ZMod p) X)

/-- The block length of the code family is twice the number of columns of the system. -/
lemma card_codeFamily (F : Type) [Field F] [Algebra (ZMod p) F] :
    Fintype.card (L.codeFamily F).M = 2 * Fintype.card L.ι := by
  show Fintype.card (L.ι ⊕ L.ι) = _
  rw [Fintype.card_sum]
  ring

/-- Extension of scalars does not change the distance from the target to the code. -/
lemma codeDist_codeFamily (F : Type) [Field F] [DecidableEq F] [Algebra (ZMod p) F] (x : X) :
    CodeFamily.codeDist ((L.codeFamily F).target x) (L.codeFamily F).code =
      CodeFamily.codeDist (L.codeTarget x) L.code :=
  CodeFamily.codeDist_extend F L.toCodeFamily x

end LinearSystemFamily

namespace QuadraticVerifier

variable {p : ℕ} [hp : Fact p.Prime]

namespace Tables

variable {V : QuadraticVerifier p} {δ : ℝ}

/-- **Theorem 5.1 for codes**, for the code of the paper: for every finite field `F` of
characteristic `p`, every `0 < ε < 1`, every quadratic verifier `V` over `𝔽_p` and every choice
of tables `T`, the code family `T.codeFamily F` has block length `M ≤ (S + 1)^C` with
`C = sizeExp p (1 - ε)`, and with the radius `R` equal to the number of blocks of the fixed
linear system, `x ∈ L(V)` implies `dist(t_x, 𝒞) ≤ R` and `x ∉ L(V)` implies
`dist(t_x, 𝒞) > M^{1 - ε} · R`. -/
private theorem codeFamily_hasGap (F : Type) [Field F] [DecidableEq F] [Algebra (ZMod p) F] {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (T : V.Tables (1 - ε)) :
    (T.codeFamily F).HasGap T.system.numBlocks ε V.Language (V.S + 1) (sizeExp p (1 - ε)) := by
  have hS1 : 1 ≤ V.S := by have := V.n_succ_le; omega
  obtain ⟨hL, hgb, hDpos, hsize⟩ := T.system_spec (by linarith : 1 - ε < 1)
  have hn1 : 1 ≤ Fintype.card T.system.ι := by
    rw [T.system.card_ι]
    exact Nat.mul_pos hDpos (by omega)
  obtain ⟨h64, hC⟩ := params_spec p (δ := 1 - ε) (by linarith) (by linarith) V.S
    (Fintype.card T.system.ι) hS1 hn1 hsize
  have hM : Fintype.card (T.codeFamily F).M = 2 * Fintype.card T.system.ι :=
    T.system.card_codeFamily F
  have hdist : ∀ x, CodeFamily.codeDist ((T.codeFamily F).target x) (T.codeFamily F).code =
      CodeFamily.codeDist (T.system.codeTarget x) T.system.code :=
    T.system.codeDist_codeFamily F
  have hM4 : Fintype.card (T.codeFamily F).M ≤ 4 * Fintype.card T.system.ι := by omega
  have hMδ : 16 * (Fintype.card (T.codeFamily F).M : ℝ) ^ (1 - ε) ≤
      (((V.S + 1) ^ gapExp p (1 - ε) : ℕ) : ℝ) :=
    rpow_le_of_le_four_mul (by linarith) (by linarith) hM4 h64
  have hDR : (0 : ℝ) < T.system.numBlocks := by exact_mod_cast hDpos
  refine ⟨hDpos, by omega, by omega, ?_, ?_⟩
  · intro x hx
    rw [hdist]
    exact T.system.codeDist_le_of_yes (hL.1 x hx)
  · intro x hx
    rw [hdist]
    have hlt : (V.S + 1) ^ gapExp p (1 - ε) * T.system.numBlocks <
        CodeFamily.codeDist (T.system.codeTarget x) T.system.code :=
      T.system.lt_codeDist_of_no hgb hDpos (hL.2 x hx)
    calc (Fintype.card (T.codeFamily F).M : ℝ) ^ (1 - ε) * (T.system.numBlocks : ℝ)
        ≤ (((V.S + 1) ^ gapExp p (1 - ε) : ℕ) : ℝ) * T.system.numBlocks := by
          gcongr
          linarith [Real.rpow_nonneg (Nat.cast_nonneg (Fintype.card (T.codeFamily F).M)) (1 - ε)]
      _ < CodeFamily.codeDist (T.system.codeTarget x) T.system.code := by exact_mod_cast hlt

end Tables

end QuadraticVerifier

end LatticePrepro

open LatticePrepro
open LatticePrepro.QuadraticVerifier
variable {p : ℕ} [hp : Fact p.Prime]
open LatticePrepro.QuadraticVerifier.Tables
variable {V : QuadraticVerifier p} {δ : ℝ}
theorem solution (F : Type) [Field F] [DecidableEq F] [Algebra (ZMod p) F] {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (T : V.Tables (1 - ε)) :
    (T.codeFamily F).HasGap T.system.numBlocks ε V.Language (V.S + 1) (sizeExp p (1 - ε)) :=
  @LatticePrepro.QuadraticVerifier.Tables.codeFamily_hasGap p _ V F _ _ _ ε hε hε1 T

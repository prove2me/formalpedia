-- Prove2me | solution 1 for LatticePrepro.code_gap
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T15:54:44.850717+00:00
-- url     : https://prove2.me/submissions/cfa1bb84-b809-40cc-90d2-569beca3e4b6

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Lattices
import Definitions.Def_LatticePrepro_Lattices_Distance
import Definitions.Def_LatticePrepro_Lattices_Mathlib
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
import Definitions.Def_LatticePrepro_Main
import Theorems.Thm_LatticePrepro_CodeFamily_codeDist_extend
import Theorems.Thm_LatticePrepro_LinearSystemFamily_code_no
import Theorems.Thm_LatticePrepro_LinearSystemFamily_code_yes
import Theorems.Thm_LatticePrepro_exists_gapReduction
import Theorems.Thm_LatticePrepro_params_spec

namespace LatticePrepro end LatticePrepro

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

/-- The code family of Lemma 3.11 over the prime field. -/
noncomputable def LinearSystemFamily.toCodeFamily : CodeFamily (ZMod p) X where
  M := L.ι ⊕ L.ι
  code := L.code
  target := L.codeTarget

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

lemma momentAxes_spec {δ : ℝ} (hδ1 : δ < 1) :
    1 ≤ momentAxes δ ∧ δ * (momentAxes δ + 1) < momentAxes δ := by
  refine ⟨by unfold momentAxes; omega, ?_⟩
  have h1δ : 0 < 1 - δ := by linarith
  have hm : δ / (1 - δ) < momentAxes δ := by
    unfold momentAxes
    push_cast
    linarith [Nat.le_ceil (δ / (1 - δ))]
  rw [div_lt_iff₀ h1δ] at hm
  nlinarith

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

/-- **Theorem 5.1 for codes**, with the explicit exponent `C = sizeExp p (1 - ε)`: for every
finite field `F` of characteristic `p`, every `0 < ε < 1` and every quadratic verifier `V` over
`𝔽_p`, there is a fixed code of block length `M ≤ (S + 1)^C` with gap `M^{1 - ε}` for `L(V)`. -/
private theorem code_gap (p : ℕ) [hp : Fact p.Prime] (F : Type) [Field F] [Fintype F]
    [DecidableEq F] [Algebra (ZMod p) F] (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (V : QuadraticVerifier p) :
    Nonempty (CodeGap F ε V.Language (V.S + 1) (sizeExp p (1 - ε))) := by
  have hm := (momentAxes_spec (δ := 1 - ε) (by linarith)).1
  have hS1 : 1 ≤ V.S := by have := V.n_succ_le; omega
  obtain ⟨⟨L, hL, hgb, -, hDpos, hsize⟩⟩ := exists_gapReduction p V
    ((V.S + 1) ^ gapExp p (1 - ε)) (momentAxes (1 - ε)) (Nat.one_le_pow _ _ (by omega)) hm
  set n := Fintype.card L.ι with hn
  have hn1 : 1 ≤ n := by
    rw [hn, L.card_ι]
    exact Nat.mul_pos hDpos (by omega)
  obtain ⟨h64, hC⟩ := params_spec p (δ := 1 - ε) (by linarith) (by linarith) V.S n hS1 hn1 hsize
  set g := (V.S + 1) ^ gapExp p (1 - ε) with hg
  -- the code over `F`
  set 𝒞 := (L.toCodeFamily).extend F with h𝒞
  have hM : Fintype.card 𝒞.M = Fintype.card (L.ι ⊕ L.ι) := rfl
  have hdist : ∀ x, CodeFamily.codeDist (𝒞.target x) 𝒞.code =
      CodeFamily.codeDist (L.codeTarget x) L.code := fun x => CodeFamily.codeDist_extend F _ x
  have hM4 : Fintype.card 𝒞.M ≤ 4 * n := by rw [hM, Fintype.card_sum]; omega
  have hMδ : 16 * (Fintype.card 𝒞.M : ℝ) ^ (1 - ε) ≤ g :=
    rpow_le_of_le_four_mul (by linarith) (by linarith) hM4 h64
  have hDR : (0 : ℝ) < L.numBlocks := by exact_mod_cast hDpos
  have hyes : ∀ x ∈ V.Language, CodeFamily.codeDist (𝒞.target x) 𝒞.code ≤ L.numBlocks := by
    intro x hx
    rw [hdist]
    exact L.codeDist_le_of_yes (hL.1 x hx)
  have hno : ∀ x ∉ V.Language,
      (Fintype.card 𝒞.M : ℝ) ^ (1 - ε) * L.numBlocks <
        CodeFamily.codeDist (𝒞.target x) 𝒞.code := by
    intro x hx
    rw [hdist]
    have hlt : g * L.numBlocks < CodeFamily.codeDist (L.codeTarget x) L.code :=
      L.lt_codeDist_of_no hgb hDpos (hL.2 x hx)
    calc (Fintype.card 𝒞.M : ℝ) ^ (1 - ε) * (L.numBlocks : ℝ)
        ≤ (g : ℝ) * L.numBlocks := by
          gcongr
          linarith [Real.rpow_nonneg (Nat.cast_nonneg (Fintype.card 𝒞.M)) (1 - ε)]
      _ < CodeFamily.codeDist (L.codeTarget x) L.code := by exact_mod_cast hlt
  refine ⟨⟨𝒞, L.numBlocks, hDpos, ?_, ?_, hyes, hno⟩⟩
  · rw [hM, Fintype.card_sum]; omega
  · rw [hM, Fintype.card_sum]; omega

end LatticePrepro

open LatticePrepro
theorem solution (p : ℕ) [hp : Fact p.Prime] (F : Type) [Field F] [Fintype F]
    [DecidableEq F] [Algebra (ZMod p) F] (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (V : QuadraticVerifier p) :
    Nonempty (CodeGap F ε V.Language (V.S + 1) (sizeExp p (1 - ε))) :=
  @LatticePrepro.code_gap p _ F _ _ _ _ ε hε hε1 V

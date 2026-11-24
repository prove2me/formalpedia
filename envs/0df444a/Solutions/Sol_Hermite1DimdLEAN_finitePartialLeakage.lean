-- Prove2me | solution 1 for Hermite1DimdLEAN.finitePartialLeakage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:44:35.938933+00:00
-- url     : https://prove2.me/submissions/97b58801-d239-44ba-9f13-2bd6c0002925

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_MissingMathlib
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_BlockLocalization
public import Theorems.Thm_Hermite1DimdLEAN_blockDecompositionNorm
public import Theorems.Thm_Hermite1DimdLEAN_explicitLocalAndFarSupport
public import Theorems.Thm_Hermite1DimdLEAN_blockLocalization
public import Theorems.Thm_Hermite1DimdLEAN_shellCountingFormula
public import Theorems.Thm_Hermite1DimdLEAN_annulusParseval
public import Theorems.Thm_Hermite1DimdLEAN_finiteParseval
public import Theorems.Thm_HermiteLEAN_polynomial_times_gaussian_le_gaussian
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


section
@[expose] public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
namespace Hermite1DimdLEAN
private lemma mem_squareBlock_iff_blockIndexMulti_eq
    {d : ℕ} (α ℓ : MultiIndex d) :
    α ∈ squareBlock ℓ ↔ blockIndexMulti α = ℓ := by
  constructor
  · intro h
    funext q
    have hq : α q ∈ HermiteLEAN.squareBlock (ℓ q) := h q
    rw [HermiteLEAN.squareBlock, Finset.mem_Ico] at hq
    exact ((Nat.eq_sqrt).2 (by simpa [Nat.pow_two] using hq)).symm
  · intro h q
    rw [HermiteLEAN.squareBlock, Finset.mem_Ico]
    have hq : Nat.sqrt (α q) = ℓ q := by
      simpa [blockIndexMulti, HermiteLEAN.blockIndex] using congrArg (fun f => f q) h
    exact by simpa [Nat.pow_two] using (Nat.eq_sqrt).1 hq.symm
private lemma blockPart_support_eq_filter
    {d : ℕ} (G : FiniteHermiteSum d) (ℓ : MultiIndex d) :
    (blockPart ℓ G).support = G.support.filter (fun α => blockIndexMulti α = ℓ) := by
  ext α
  simp [FiniteHermiteSum.support, blockPart, Finsupp.mem_support_iff,
    mem_squareBlock_iff_blockIndexMulti_eq, and_comm]
private lemma blockwise_regroup
    {d : ℕ} (G : FiniteHermiteSum d) (w : MultiIndex d → ℝ) :
    ∑ ℓ ∈ G.support.image blockIndexMulti,
        ∑ α ∈ (blockPart ℓ G).support, ‖(blockPart ℓ G).coeff α‖ ^ 2 * w α =
      ∑ α ∈ G.support, ‖G.coeff α‖ ^ 2 * w α := by
  classical
  have hterm :
      ∀ ℓ ∈ G.support.image blockIndexMulti,
        ∑ α ∈ (blockPart ℓ G).support, ‖(blockPart ℓ G).coeff α‖ ^ 2 * w α =
          ∑ α ∈ G.support.filter (fun α => blockIndexMulti α = ℓ), ‖G.coeff α‖ ^ 2 * w α := by
    intro ℓ _
    rw [blockPart_support_eq_filter]
    refine Finset.sum_congr rfl fun α hα => ?_
    have hblock : blockIndexMulti α = ℓ := (Finset.mem_filter.mp hα).2
    have hsq : α ∈ squareBlock ℓ := (mem_squareBlock_iff_blockIndexMulti_eq α ℓ).mpr hblock
    simp [blockPart, Finsupp.onFinset_apply, hsq]
  rw [Finset.sum_congr rfl hterm, Finset.sum_fiberwise_eq_sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  refine Finset.filter_true_of_mem fun α hα => ?_
  exact Finset.mem_image.mpr ⟨α, hα, rfl⟩
private lemma blockPart_coeff_eq_zero_of_not_mem_support_image
    {d : ℕ} (G : FiniteHermiteSum d) (ℓ α : MultiIndex d)
    (hℓ : ℓ ∉ G.support.image blockIndexMulti) :
    (blockPart ℓ G).coeff α = 0 := by
  by_cases hb : α ∈ squareBlock ℓ
  · have hidx : blockIndexMulti α = ℓ := (mem_squareBlock_iff_blockIndexMulti_eq α ℓ).mp hb
    by_cases hsupp : α ∈ G.support
    · exact absurd (Finset.mem_image.mpr ⟨α, hsupp, hidx⟩) hℓ
    · have hcoeff : G.coeff α = 0 := by
        simpa [FiniteHermiteSum.support, Finsupp.mem_support_iff] using hsupp
      simp [blockPart, Finsupp.onFinset_apply, hb, hcoeff]
  · simp [blockPart, Finsupp.onFinset_apply, hb]
private lemma hermiteNormSq_blockPart_eq_zero_of_not_mem_support_image
    {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) (ℓ : MultiIndex d)
    (hℓ : ℓ ∉ G.support.image blockIndexMulti) :
    hermiteNormSq κ (blockPart ℓ G) = 0 := by
  rw [finiteParseval]
  refine Finset.sum_eq_zero fun α _ => ?_
  simp [blockPart_coeff_eq_zero_of_not_mem_support_image G ℓ α hℓ]
private lemma tsum_hermiteNormSq_blockPart_eq_sum_support_image
    {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) :
    ∑' ℓ : MultiIndex d, hermiteNormSq κ (blockPart ℓ G) =
      Finset.sum (G.support.image blockIndexMulti) (fun ℓ => hermiteNormSq κ (blockPart ℓ G)) :=
  tsum_eq_sum
    (fun ℓ hℓ => hermiteNormSq_blockPart_eq_zero_of_not_mem_support_image κ G ℓ hℓ)
private lemma blockDecompositionNorm_sum_support_image
    {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) :
    hermiteNormSq κ G =
      Finset.sum (G.support.image blockIndexMulti) (fun ℓ => hermiteNormSq κ (blockPart ℓ G)) := by
  rw [blockDecompositionNorm, tsum_hermiteNormSq_blockPart_eq_sum_support_image]
private lemma hermiteNormSq_nonneg
    {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) :
    0 ≤ hermiteNormSq κ G := by
  rw [finiteParseval]
  positivity
private lemma annulusMass_blockDecomposition_sum_support_image
    {d : ℕ} (κ : MultiIndex d) (j : MultiIndex d) (G : FiniteHermiteSum d) :
    annulusMass j (evalHermiteSum κ G) =
      Finset.sum (G.support.image blockIndexMulti)
        (fun ℓ => annulusMass j (evalHermiteSum κ (blockPart ℓ G))) := by
  classical
  rw [annulusParseval]
  simp_rw [annulusParseval]
  exact (blockwise_regroup G (fun α => annulusMass j (PhiKappaAlpha κ α))).symm
private lemma blockPart_remainderPart_coeff
    {d : ℕ} (j ℓ α : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d) :
    (blockPart ℓ (remainderPart j M G)).coeff α =
      if M < blockDistance j ℓ then (blockPart ℓ G).coeff α else 0 := by
  by_cases hb : α ∈ squareBlock ℓ
  · have hidx : blockIndexMulti α = ℓ :=
      (mem_squareBlock_iff_blockIndexMulti_eq α ℓ).mp hb
    by_cases hfar : M < blockDistance j ℓ <;>
      simp [blockPart, remainderPart, Finsupp.onFinset_apply, farCoeffSet,
        FiniteHermiteSum.support, hb, hfar, hidx]
  · by_cases hfar : M < blockDistance j ℓ <;>
      simp [blockPart, remainderPart, Finsupp.onFinset_apply, hb, hfar]
private lemma hermiteNormSq_blockPart_remainderPart
    {d : ℕ} (κ j ℓ : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d) :
    hermiteNormSq κ (blockPart ℓ (remainderPart j M G)) =
      if M < blockDistance j ℓ then hermiteNormSq κ (blockPart ℓ G) else 0 := by
  by_cases hfar : M < blockDistance j ℓ
  · rw [finiteParseval, finiteParseval, if_pos hfar]
    have hsupport :
        (blockPart ℓ (remainderPart j M G)).support = (blockPart ℓ G).support := by
      ext α
      simp [FiniteHermiteSum.support, Finsupp.mem_support_iff, blockPart_remainderPart_coeff, hfar]
    rw [hsupport]
    refine Finset.sum_congr rfl ?_
    intro α hα
    simp [blockPart_remainderPart_coeff, hfar]
  · rw [finiteParseval, if_neg hfar]
    refine Finset.sum_eq_zero ?_
    intro α hα
    simp [blockPart_remainderPart_coeff, hfar]
private lemma remainderPart_annulus_blockwise_bound
    {d : ℕ} (κ : MultiIndex d) {C c B : ℝ}
    (hC : 0 ≤ C)
    (hloc :
      ∀ j ℓ : MultiIndex d, ∀ G : FiniteHermiteSum d,
        annulusMass j (evalHermiteSum κ (blockPart ℓ G)) ≤
          C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) *
            hermiteNormSq κ (blockPart ℓ G))
    (j : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d) :
    annulusMass j (evalHermiteSum κ (remainderPart j M G)) ≤
      Finset.sum ((remainderPart j M G).support.image blockIndexMulti)
        (fun ℓ =>
          if M < blockDistance j ℓ then
            C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) *
              hermiteNormSq κ (blockPart ℓ G)
          else 0) := by
  rw [annulusMass_blockDecomposition_sum_support_image]
  exact Finset.sum_le_sum (fun ℓ hℓ => by
    have hbase := hloc j ℓ (remainderPart j M G)
    by_cases hfar : M < blockDistance j ℓ
    · rw [hermiteNormSq_blockPart_remainderPart (κ := κ) (j := j) (ℓ := ℓ) (M := M)
        (G := G), if_pos hfar] at hbase
      simpa [hfar] using hbase
    · rw [hermiteNormSq_blockPart_remainderPart (κ := κ) (j := j) (ℓ := ℓ) (M := M)
        (G := G), if_neg hfar] at hbase
      have hle0 :
          annulusMass j (evalHermiteSum κ (blockPart ℓ (remainderPart j M G))) ≤ 0 := by
        simpa using hbase
      have hnonneg : 0 ≤ annulusMass j (evalHermiteSum κ (blockPart ℓ (remainderPart j M G))) := by
        unfold annulusMass
        positivity
      have hzero :
          annulusMass j (evalHermiteSum κ (blockPart ℓ (remainderPart j M G))) = 0 :=
        le_antisymm hle0 hnonneg
      have hright_nonneg :
          0 ≤ C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) *
            hermiteNormSq κ (blockPart ℓ G) := by
        have hnorm_nonneg : 0 ≤ hermiteNormSq κ (blockPart ℓ G) :=
          hermiteNormSq_nonneg κ (blockPart ℓ G)
        positivity
      simp [hfar, hzero])
private lemma sup_coord_exists
    {d : ℕ} (hd : d ≠ 0) (j ℓ : MultiIndex d) :
    ∃ q0 : Fin d, blockDistance j ℓ = Nat.dist (j q0) (ℓ q0) := by
  let q0 : Fin d := ⟨0, Nat.pos_of_ne_zero hd⟩
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨q0, Finset.mem_univ q0⟩
  have hbd_eq :
      blockDistance j ℓ = Finset.univ.sup' hne (fun q : Fin d => Nat.dist (j q) (ℓ q)) := by
    rw [blockDistance, Finset.sup'_eq_sup hne]
  rw [hbd_eq]
  rcases Finset.exists_mem_eq_sup (s := (Finset.univ : Finset (Fin d))) hne
      (f := fun q : Fin d => Nat.dist (j q) (ℓ q)) with ⟨q0, hq0, hsup⟩
  refine ⟨q0, ?_⟩
  simpa [Finset.sup'_eq_sup hne] using hsup
private lemma shell_offset_mem_cube_sdiff
    {d : ℕ} (hd : d ≠ 0) {ℓ j : MultiIndex d} {r : ℕ}
    (hj : blockDistance j ℓ = r) (hr : 1 ≤ r) :
    let x : Fin d → ℤ := fun q => (j q : ℤ) - ℓ q
    let cube : Finset (Fin d → ℤ) :=
      Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(r : ℤ)) (r : ℤ))
    let inner : Finset (Fin d → ℤ) :=
      Fintype.piFinset (fun _ : Fin d => Finset.Icc (-((r - 1 : ℕ) : ℤ)) (((r - 1 : ℕ) : ℤ)))
    x ∈ cube ∧ x ∉ inner := by
  dsimp
  constructor
  · change (fun q : Fin d => (j q : ℤ) - ℓ q) ∈
        Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(r : ℤ)) (r : ℤ))
    rw [Fintype.mem_piFinset]
    intro q
    have hq : Nat.dist (j q) (ℓ q) ≤ r := by
      rw [← hj]
      exact (Finset.univ : Finset (Fin d)).le_sup (f := fun q' : Fin d => Nat.dist (j q') (ℓ q'))
        (Finset.mem_univ q)
    simp [Finset.mem_Icc]
    by_cases hle : j q ≤ ℓ q
    · rw [Nat.dist_eq_sub_of_le hle] at hq
      omega
    · have hle' : ℓ q ≤ j q := Nat.le_of_lt (Nat.lt_of_not_ge hle)
      rw [Nat.dist_eq_sub_of_le_right hle'] at hq
      omega
  · intro hx
    change (fun q : Fin d => (j q : ℤ) - ℓ q) ∈
        Fintype.piFinset
          (fun _ : Fin d => Finset.Icc (-((r - 1 : ℕ) : ℤ)) (((r - 1 : ℕ) : ℤ))) at hx
    rw [Fintype.mem_piFinset] at hx
    rcases sup_coord_exists hd j ℓ with ⟨q0, hq0⟩
    have hdist : Nat.dist (j q0) (ℓ q0) = r := by simpa [hj] using hq0.symm
    have hxq := hx q0
    simp [Finset.mem_Icc] at hxq
    by_cases hle : j q0 ≤ ℓ q0
    · rw [Nat.dist_eq_sub_of_le hle] at hdist
      omega
    · have hle' : ℓ q0 ≤ j q0 := Nat.le_of_lt (Nat.lt_of_not_ge hle)
      rw [Nat.dist_eq_sub_of_le_right hle'] at hdist
      omega
private lemma cube_boundary_card
    (d r : ℕ) (hr : 1 ≤ r) :
    let cube : Finset (Fin d → ℤ) := Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(r : ℤ)) (r :
        ℤ))
    let inner : Finset (Fin d → ℤ) :=
      Fintype.piFinset (fun _ : Fin d => Finset.Icc (-((r - 1 : ℕ) : ℤ)) (((r - 1 : ℕ) : ℤ)))
    (cube \ inner).card = shellCardinality d r := by
  dsimp
  have hsubset :
      Fintype.piFinset (fun _ : Fin d => Finset.Icc (-((r - 1 : ℕ) : ℤ)) (((r - 1 : ℕ) : ℤ))) ⊆
        Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(r : ℤ)) (r : ℤ)) := by
    intro x hx
    rw [Fintype.mem_piFinset] at hx ⊢
    intro q
    have hxq := hx q
    simp [Finset.mem_Icc] at hxq ⊢
    omega
  have hcube : (Finset.Icc (-(r : ℤ)) (r : ℤ)).card = 2 * r + 1 := by
    simp [Int.card_Icc]
    omega
  have hinner : (Finset.Icc (-((r - 1 : ℕ) : ℤ)) (((r - 1 : ℕ) : ℤ))).card = 2 * r - 1 := by
    simp [Int.card_Icc]
    omega
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsubset, Fintype.card_piFinset_const,
    Fintype.card_piFinset_const, hcube, hinner, shellCardinality]
private lemma shellSubtype_injects
    {d : ℕ} (hd : d ≠ 0) (ℓ : MultiIndex d) {r : ℕ} (hr : 1 ≤ r) :
    ∃ f : {j : MultiIndex d // blockDistance j ℓ = r} → {x // x ∈ shellFinset d r},
      Function.Injective f := by
  refine ⟨fun j => ⟨(fun q => (j.1 q : ℤ) - ℓ q), by
      simpa [shellFinset, Finset.mem_sdiff] using shell_offset_mem_cube_sdiff hd j.2 hr⟩, ?_⟩
  intro a b hab
  apply Subtype.ext
  funext q
  have hq : (a.1 q : ℤ) - ℓ q = (b.1 q : ℤ) - ℓ q := by simpa using congrArg (fun x => x.1 q) hab
  omega
private lemma shellSubtype_isEmpty
    (ℓ : MultiIndex 0) {r : ℕ} (hr : 1 ≤ r) :
    IsEmpty {j : MultiIndex 0 // blockDistance j ℓ = r} := by
  refine ⟨fun j => ?_⟩
  have hd0 : blockDistance j.1 ℓ = 0 := by simp [blockDistance]
  have hjr := j.2
  omega
private lemma finiteShellSubtype
    {d : ℕ} (ℓ : MultiIndex d) {r : ℕ} (hr : 1 ≤ r) :
    Finite {j : MultiIndex d // blockDistance j ℓ = r} := by
  by_cases hd : d = 0
  · subst hd
    let := shellSubtype_isEmpty ℓ hr
    infer_instance
  · obtain ⟨f, hf⟩ := shellSubtype_injects hd ℓ hr
    exact Finite.of_injective f hf
private lemma sharpShellCount_of_pos
    {d : ℕ} (ℓ : MultiIndex d) {r : ℕ} (hr : 1 ≤ r) :
    Nat.card {j : MultiIndex d // blockDistance j ℓ = r} ≤ shellCardinality d r := by
  by_cases hd : d = 0
  · subst hd
    let := shellSubtype_isEmpty ℓ hr
    simp_all
  · obtain ⟨f, hf⟩ := shellSubtype_injects hd ℓ hr
    have hshell : Nat.card {x // x ∈ shellFinset d r} = shellCardinality d r := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      exact cube_boundary_card d r hr
    let := finiteShellSubtype ℓ hr
    exact le_trans (Nat.card_le_card_of_injective f hf) (le_of_eq hshell)
private lemma shell_cardinality_bound_filter
    {d : ℕ} (ℓ : MultiIndex d) (r : ℕ) (s : Finset (MultiIndex d))
    (hr : 1 ≤ r) :
    (((s.filter fun j => blockDistance j ℓ = r).card : ℕ) : ℝ) ≤ shellCardinality d r := by
  by_cases hd : d = 0
  · subst hd
    have hfilter0 : s.filter (fun j => blockDistance j ℓ = r) = ∅ := by
      ext j
      simp only [mem_filter, notMem_empty, iff_false, not_and]
      intro hj hEq
      have hdist0 : blockDistance j ℓ = 0 := by simp [blockDistance]
      have : r = 0 := by simpa [hdist0] using hEq.symm
      omega
    simp [hfilter0, shellCardinality]
  · let f :
        {j // j ∈ s.filter fun j => blockDistance j ℓ = r} →
        {j : MultiIndex d // blockDistance j ℓ = r} :=
      fun j => ⟨j.1, (Finset.mem_filter.mp j.2).2⟩
    have hf : Function.Injective f := by
      intro a b hab
      cases a
      cases b
      cases hab
      rfl
    let := finiteShellSubtype ℓ hr
    have hcard :=
      Nat.card_le_card_of_injective f hf
    have hfilter :
        Nat.card {j // j ∈ s.filter fun j => blockDistance j ℓ = r} =
          (s.filter fun j => blockDistance j ℓ = r).card := by
      rw [Nat.card_eq_fintype_card]
      simp
    rw [← hfilter]
    calc
      ((Nat.card {j // j ∈ s.filter fun j => blockDistance j ℓ = r} : ℕ) : ℝ)
          ≤ Nat.card {j : MultiIndex d // blockDistance j ℓ = r} := by exact_mod_cast hcard
      _ ≤ shellCardinality d r := by exact_mod_cast sharpShellCount_of_pos ℓ hr
private lemma summable_exp_neg_mul_sq {a : ℝ} (ha : 0 < a) :
    Summable (fun r : ℕ => Real.exp (-a * (r : ℝ) ^ 2)) := by
  refine Real.summable_exp_nat_mul_of_ge ?_ ?_
  · linarith only [ha]
  · intro i
    have hreal : (i : ℝ) ≤ (i : ℝ) * (i : ℝ) := by exact_mod_cast Nat.le_mul_self i
    simpa [pow_two] using hreal
private lemma polynomialGaussianTailMajorant_summable
    {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Summable (fun r : ℕ => (1 + (r : ℝ) ^ k) * Real.exp (-a * (r : ℝ) ^ 2)) := by
  obtain ⟨C, hCpos, hbound⟩ :=
    HermiteLEAN.polynomial_times_gaussian_le_gaussian ha k
  exact Summable.of_nonneg_of_le
      (f := fun r : ℕ => C * Real.exp (-(a / 2) * (r : ℝ) ^ 2))
      (g := fun r : ℕ => (1 + (r : ℝ) ^ k) * Real.exp (-a * (r : ℝ) ^ 2))
      (fun r => by positivity)
      (fun r => hbound (r : ℝ) (by positivity))
      ((summable_exp_neg_mul_sq (by linarith only [ha])).mul_left C)
private lemma tailIndicator_tendsto_zero
    {u : ℕ → ℝ} (hu : Summable u) :
    Filter.Tendsto
      (fun M : ℕ => ∑' r : ℕ, if M + 1 ≤ r then u r else 0)
      Filter.atTop (nhds 0) := by
  have htail :
      Filter.Tendsto (fun M : ℕ => ∑' k : ℕ, u (k + (M + 1)))
        Filter.atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (tendsto_sum_nat_add u).comp (Filter.tendsto_add_atTop_nat 1)
  refine htail.congr' ?_
  filter_upwards [] with M
  let p : ℕ → ℝ := fun r => if r < M + 1 then u r else 0
  let v : ℕ → ℝ := fun r => if M < r then u r else 0
  have hp : Summable p := by
    refine (hu.indicator {r : ℕ | r < M + 1}).congr ?_
    intro r
    simp [p, Set.indicator]
  have hv : Summable v := by
    refine (hu.indicator {r : ℕ | M < r}).congr ?_
    intro r
    simp [v, Set.indicator]
  have hp_tsum :
      (∑' r : ℕ, p r) = ∑ i ∈ Finset.range (M + 1), u i := by
    calc
      (∑' r : ℕ, p r) = ∑ r ∈ Finset.range (M + 1), p r := tsum_eq_sum (by
        intro b hb
        simp only [p]
        rw [if_neg]
        simpa [Finset.mem_range] using hb)
      _ = ∑ r ∈ Finset.range (M + 1), u r := by
        apply Finset.sum_congr rfl
        intro r hr
        simp only [p, if_pos (Finset.mem_range.mp hr)]
  have hpv : ∀ r : ℕ, p r + v r = u r := by
    intro r
    dsimp [p, v]
    by_cases h : r < M + 1
    · rw [if_pos h, if_neg]
      · exact add_zero _
      · omega
    · rw [if_neg h, if_pos]
      · exact zero_add _
      · omega
  have h1 :
      (∑ i ∈ Finset.range (M + 1), u i) +
          (∑' r : ℕ, if M < r then u r else 0) =
        ∑' i : ℕ, u i := by
    rw [← hp_tsum, ← hp.tsum_add hv]
    exact tsum_congr hpv
  have h2 :
      (∑ i ∈ Finset.range (M + 1), u i) +
          (∑' k : ℕ, u (k + (M + 1))) =
        ∑' i : ℕ, u i := by simpa using hu.sum_add_tsum_nat_add (M + 1)
  have hEq : (∑' r : ℕ, if M < r then u r else 0) = ∑' k : ℕ, u (k + (M + 1)) := by
    linarith only [h1, h2]
  simpa [Nat.succ_le_iff] using hEq.symm
private lemma shellExp_global_majorant
    {d : ℕ} {c B : ℝ} (hc : 0 < c) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 < K ∧
      ∀ r : ℕ,
        (shellCardinality d r : ℝ) *
            Real.exp (-(c) * max ((r : ℝ) - B) 0 ^ 2)
          ≤ K * (1 + (r : ℝ) ^ d) * Real.exp (-(c / 8) * (r : ℝ) ^ 2) := by
  refine ⟨(3 : ℝ) ^ d * Real.exp (c * B ^ 2), by positivity, ?_⟩
  intro r
  have hshell :
      (shellCardinality d r : ℝ) ≤ (3 : ℝ) ^ d * (1 + (r : ℝ) ^ d) := by
    by_cases hr0 : r = 0
    · subst hr0
      have hzero : (shellCardinality d 0 : ℝ) ≤ 1 := by
        exact_mod_cast (by simp [shellCardinality] : shellCardinality d 0 ≤ 1)
      have hpow1 : (1 : ℝ) ≤ (3 : ℝ) ^ d := one_le_pow₀ (by norm_num)
      have hfac : (1 : ℝ) ≤ 1 + (((0 : ℕ) : ℝ) ^ d) := by
        linarith only [show (0 : ℝ) ≤ (((0 : ℕ) : ℝ) ^ d) by positivity]
      linarith only [hzero, hpow1, hfac, mul_le_mul hpow1 hfac (by norm_num) (by positivity)]
    · have hr1 : 1 ≤ r := Nat.succ_le_of_lt (Nat.pos_iff_ne_zero.mpr hr0)
      have hs : (shellCardinality d r : ℝ) ≤ ((2 * r + 1) ^ d : ℕ) := by
        exact_mod_cast shellCountingFormula d r
      have hbase : (2 * r + 1 : ℝ) ≤ 3 * r := by
        linarith only [
          hr1, show (1 : ℝ) ≤ r by exact_mod_cast hr1
        ]
      have hpow : (2 * r + 1 : ℝ) ^ d ≤ (3 * r : ℝ) ^ d := by gcongr
      have hshell' : (shellCardinality d r : ℝ) ≤ (3 : ℝ) ^ d * (r : ℝ) ^ d := by
        calc
          (shellCardinality d r : ℝ) ≤ (2 * r + 1 : ℝ) ^ d := by exact_mod_cast hs
          _ ≤ (3 * r : ℝ) ^ d := hpow
          _ = (3 : ℝ) ^ d * (r : ℝ) ^ d := by rw [mul_pow]
      have hrpow_nonneg : 0 ≤ (r : ℝ) ^ d := by positivity
      exact le_trans hshell' <| mul_le_mul_of_nonneg_left (by linarith only []) (by positivity)
  have hexp :
      Real.exp (-(c) * max ((r : ℝ) - B) 0 ^ 2) ≤
        Real.exp (c * B ^ 2) * Real.exp (-(c / 8) * (r : ℝ) ^ 2) := by
    have hr_nonneg : 0 ≤ (r : ℝ) := by positivity
    have hsq :
        (r : ℝ) ^ 2 / 8 - B ^ 2 ≤ max ((r : ℝ) - B) 0 ^ 2 := by
      by_cases hsmall : (r : ℝ) ≤ 2 * B
      · have hrhs_nonpos : (r : ℝ) ^ 2 / 8 - B ^ 2 ≤ 0 := by nlinarith only [hB, hsmall]
        have hnonneg : 0 ≤ max ((r : ℝ) - B) 0 ^ 2 := by positivity
        linarith only [hrhs_nonpos, hnonneg]
      · have hlarge : 2 * B < (r : ℝ) := by linarith only [hsmall]
        have hhalf : (r : ℝ) / 2 ≤ (r : ℝ) - B := by linarith only [hsmall]
        have hmaxeq : max ((r : ℝ) - B) 0 = (r : ℝ) - B := by
          apply max_eq_left
          linarith only [hB, hsmall]
        rw [hmaxeq]
        have hsquare_half : ((r : ℝ) / 2) ^ 2 ≤ ((r : ℝ) - B) ^ 2 := by nlinarith only [hsmall]
        nlinarith only [hsquare_half]
    have hlog :
        -(c) * max ((r : ℝ) - B) 0 ^ 2 ≤ c * B ^ 2 - (c / 8) * (r : ℝ) ^ 2 := by
          nlinarith only [
            hc, hsq
          ]
    calc
      Real.exp (-(c) * max ((r : ℝ) - B) 0 ^ 2)
        ≤ Real.exp (c * B ^ 2 - (c / 8) * (r : ℝ) ^ 2) := Real.exp_le_exp.mpr hlog
      _ = Real.exp (c * B ^ 2) * Real.exp (-(c / 8) * (r : ℝ) ^ 2) := by
          rw [← Real.exp_add]
          congr 1
          ring
  calc
    (shellCardinality d r : ℝ) * Real.exp (-(c) * max ((r : ℝ) - B) 0 ^ 2)
      ≤ ((3 : ℝ) ^ d * (1 + (r : ℝ) ^ d)) *
          (Real.exp (c * B ^ 2) * Real.exp (-(c / 8) * (r : ℝ) ^ 2)) :=
            mul_le_mul hshell hexp (by positivity) (by positivity)
    _ = ((3 : ℝ) ^ d * Real.exp (c * B ^ 2)) *
          (1 + (r : ℝ) ^ d) * Real.exp (-(c / 8) * (r : ℝ) ^ 2) := by ring
private lemma localizationLeakageSeriesSummable
    {d : ℕ} {C c B : ℝ} (hC : 0 < C) (hc : 0 < c) (hB : 0 ≤ B) :
    Summable
      (fun r : ℕ =>
        C * ((shellCardinality d r : ℝ) *
          Real.exp (-(c) * max ((r : ℝ) - B) 0 ^ 2))) := by
  obtain ⟨K, hKpos, hmajor⟩ := shellExp_global_majorant (d := d) hc hB
  have hsum : Summable (fun r : ℕ => K * (1 + (r : ℝ) ^ d) * Real.exp (-(c / 8) * (r : ℝ) ^ 2)) :=
      by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (polynomialGaussianTailMajorant_summable
        (a := c / 8)
        (by linarith only [hc])
        d).mul_left K
  exact Summable.of_nonneg_of_le
      (f := fun r : ℕ =>
        K * (1 + (r : ℝ) ^ d) * Real.exp (-(c / 8) * (r : ℝ) ^ 2) * C)
      (g := fun r : ℕ =>
        C * ((shellCardinality d r : ℝ) *
          Real.exp (-(c) * max ((r : ℝ) - B) 0 ^ 2)))
      (fun r => by positivity)
      (fun r => by
        have := hmajor r
        nlinarith only [hC, this])
      (hsum.mul_right C)
private lemma localizationLeakageCoefficient_tendsto_zero
    {d : ℕ} {C c B : ℝ} (hC : 0 < C) (hc : 0 < c) (hB : 0 ≤ B) :
    Filter.Tendsto
      (fun M : ℕ => localizationLeakageCoefficient C c B d M)
      Filter.atTop (nhds 0) := by
  have hu := localizationLeakageSeriesSummable (d := d) hC hc hB
  have htail :=
    tailIndicator_tendsto_zero
      (u := fun r : ℕ =>
        C * ((shellCardinality d r : ℝ) *
          Real.exp (-(c) * max ((r : ℝ) - B) 0 ^ 2))) hu
  refine htail.congr' ?_
  filter_upwards [] with M
  unfold localizationLeakageCoefficient
  have hterm :
      (∑' r : ℕ,
        if M + 1 ≤ r then
          C * ((shellCardinality d r : ℝ) * Real.exp (-(c) * max ((r : ℝ) - B) 0 ^ 2))
        else 0) =
      ∑' r : ℕ,
        C * (if M + 1 ≤ r then
          (shellCardinality d r : ℝ) * Real.exp (-(c) * max ((r : ℝ) - B) 0 ^ 2)
        else 0) := by
    simp_all
  rw [hterm, tsum_mul_left]
private lemma shell_sum_localizationLeakageCoefficient_bound
    {d : ℕ} {C c B : ℝ} (hC : 0 < C) (hc : 0 < c) (hB : 0 ≤ B)
    (M : ℕ) (t : Finset ℕ) :
    Finset.sum t
      (fun r =>
        (shellCardinality d r : ℝ) *
          (if M < r then C * Real.exp (-(c) * max ((r : ℝ) - B) 0 ^ 2) else 0)) ≤
      localizationLeakageCoefficient C c B d M := by
  let u : ℕ → ℝ := fun r =>
    if M + 1 ≤ r then
      C * ((shellCardinality d r : ℝ) *
        Real.exp (-(c) * max ((r : ℝ) - B) 0 ^ 2))
    else 0
  have hu_base := localizationLeakageSeriesSummable (d := d) hC hc hB
  have hu : Summable u := by
    refine Summable.of_nonneg_of_le ?_ ?_ hu_base
    · intro r
      by_cases hlt : M < r
      · simp only [Order.add_one_le_iff, neg_mul, hlt, ↓reduceIte, u]
        positivity
      · have : ¬ M + 1 ≤ r := by omega
        simp [u, hlt]
    · intro r
      by_cases hr : M + 1 ≤ r
      · by_cases hlt : M < r
        · simp [u, hlt]
        · simp_all
      · have hlt : ¬ M < r := by omega
        simp only [Order.add_one_le_iff, neg_mul, hlt, ↓reduceIte, ge_iff_le, u]
        positivity
  calc
    Finset.sum t
      (fun r =>
        (shellCardinality d r : ℝ) *
          (if M < r then C * Real.exp (-(c) * max ((r : ℝ) - B) 0 ^ 2) else 0))
      = Finset.sum t u := by
          refine Finset.sum_congr rfl fun r _ => ?_
          by_cases hMr : M < r
          · have hMr' : M + 1 ≤ r := by omega
            simp only [u, hMr, ite_true, hMr']
            ring
          · simp [u, hMr]
    _ ≤ ∑' r : ℕ, u r := by
          exact hu.sum_le_tsum _ (fun r hr => by
            by_cases hMr : M + 1 ≤ r
            · simp only [hMr, ↓reduceIte, neg_mul]
              positivity
            · by_cases hlt : M < r
              · simp_all
              · simp [hMr])
    _ = localizationLeakageCoefficient C c B d M := by
          unfold localizationLeakageCoefficient
          rw [← tsum_mul_left]
          refine tsum_congr fun r => ?_
          by_cases hMr : M + 1 ≤ r
          · simp only [u, hMr, ite_true]
          · simp only [u, hMr, ite_false, mul_zero]
private lemma finitePartialLeakage_bound_of_shell_sum_bound
    {d : ℕ} (κ : MultiIndex d) {C c B : ℝ}
    (hC : 0 ≤ C)
    (hloc :
      ∀ j ℓ : MultiIndex d, ∀ G : FiniteHermiteSum d,
        annulusMass j (evalHermiteSum κ (blockPart ℓ G)) ≤
          C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) *
            hermiteNormSq κ (blockPart ℓ G))
    (hshell :
      ∀ (M : ℕ) (ℓ : MultiIndex d) (s : Finset (MultiIndex d)),
        Finset.sum s
          (fun j =>
            if M < blockDistance j ℓ then
              C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2)
            else 0) ≤
          localizationLeakageCoefficient C c B d M)
    (s : Finset (MultiIndex d)) (M : ℕ) (G : FiniteHermiteSum d) :
    Finset.sum s (fun j => annulusMass j (evalHermiteSum κ (remainderPart j M G))) ≤
      localizationLeakageCoefficient C c B d M * hermiteNormSq κ G := by
  have hpoint :
      ∀ j : MultiIndex d,
        annulusMass j (evalHermiteSum κ (remainderPart j M G)) ≤
          Finset.sum (G.support.image blockIndexMulti)
            (fun ℓ =>
              if M < blockDistance j ℓ then
                C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) *
                  hermiteNormSq κ (blockPart ℓ G)
              else 0) := by
    intro j
    have hrem_support_subset : (remainderPart j M G).support ⊆ G.support := by
      intro α hα
      have hfar_support := (explicitLocalAndFarSupport (j := j) (M := M) (G := G)).2.2.2
      rw [hfar_support] at hα
      exact (Finset.mem_filter.mp hα).1
    have hrem_image_subset :
        (remainderPart j M G).support.image blockIndexMulti ⊆ G.support.image blockIndexMulti := by
      intro ℓ hℓ
      rcases Finset.mem_image.mp hℓ with ⟨α, hα, rfl⟩
      exact Finset.mem_image.mpr ⟨α, hrem_support_subset hα, rfl⟩
    calc
      annulusMass j (evalHermiteSum κ (remainderPart j M G))
        ≤ Finset.sum ((remainderPart j M G).support.image blockIndexMulti)
            (fun ℓ =>
              if M < blockDistance j ℓ then
                C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) *
                  hermiteNormSq κ (blockPart ℓ G)
              else 0) :=
                remainderPart_annulus_blockwise_bound (κ := κ) (hC := hC) hloc j M G
      _ ≤ Finset.sum (G.support.image blockIndexMulti)
            (fun ℓ =>
              if M < blockDistance j ℓ then
                C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) *
                  hermiteNormSq κ (blockPart ℓ G)
              else 0) := by
                exact Finset.sum_le_sum_of_subset_of_nonneg hrem_image_subset (by
                  intro ℓ hℓ hnot
                  by_cases hfar : M < blockDistance j ℓ
                  · have hexp_nonneg :
                        0 ≤ Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) := by
                      positivity
                    have hnorm_nonneg : 0 ≤ hermiteNormSq κ (blockPart ℓ G) :=
                      hermiteNormSq_nonneg κ (blockPart ℓ G)
                    simpa [hfar] using
                      (mul_nonneg (mul_nonneg hC hexp_nonneg) hnorm_nonneg)
                  · simp [hfar])
  calc
    Finset.sum s (fun j => annulusMass j (evalHermiteSum κ (remainderPart j M G)))
      ≤ Finset.sum s
          (fun j =>
            Finset.sum (G.support.image blockIndexMulti)
              (fun ℓ =>
                if M < blockDistance j ℓ then
                  C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) *
                    hermiteNormSq κ (blockPart ℓ G)
                else 0)) := by
                  refine Finset.sum_le_sum ?_
                  simp_all
    _ = Finset.sum (G.support.image blockIndexMulti)
          (fun ℓ =>
            Finset.sum s
              (fun j =>
                if M < blockDistance j ℓ then
                  C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) *
                    hermiteNormSq κ (blockPart ℓ G)
                else 0)) := by rw [Finset.sum_comm]
    _ ≤ Finset.sum (G.support.image blockIndexMulti)
          (fun ℓ => localizationLeakageCoefficient C c B d M * hermiteNormSq κ (blockPart ℓ G)) :=
              by
            refine Finset.sum_le_sum ?_
            intro ℓ hℓ
            have hnorm_nonneg : 0 ≤ hermiteNormSq κ (blockPart ℓ G) :=
              hermiteNormSq_nonneg κ (blockPart ℓ G)
            have hshell' := hshell M ℓ s
            have hfactor :
                Finset.sum s
                  (fun j =>
                    if M < blockDistance j ℓ then
                      C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) *
                        hermiteNormSq κ (blockPart ℓ G)
                    else 0) =
                  (Finset.sum s
                    (fun j =>
                      if M < blockDistance j ℓ then
                        C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2)
                      else 0)) *
                    hermiteNormSq κ (blockPart ℓ G) := by
              rw [Finset.sum_mul]
              simp_all
            rw [hfactor]
            exact mul_le_mul_of_nonneg_right hshell' hnorm_nonneg
    _ = localizationLeakageCoefficient C c B d M * hermiteNormSq κ G := by
          rw [← Finset.mul_sum, ← blockDecompositionNorm_sum_support_image]
private lemma shell_sum_bound_of_shell_cardinality_bound
    {d : ℕ} {C c B : ℝ}
    (hC : 0 ≤ C)
    (htail :
      ∀ (M : ℕ) (t : Finset ℕ),
        Finset.sum t
          (fun r =>
            (shellCardinality d r : ℝ) *
              (if M < r then C * Real.exp (-(c) * max ((r : ℝ) - B) 0 ^ 2) else 0)) ≤
          localizationLeakageCoefficient C c B d M)
    (hcard :
      ∀ (ℓ : MultiIndex d) (r : ℕ) (s : Finset (MultiIndex d)),
        1 ≤ r →
        (((s.filter fun j => blockDistance j ℓ = r).card : ℕ) : ℝ) ≤ shellCardinality d r)
    (M : ℕ) (ℓ : MultiIndex d) (s : Finset (MultiIndex d)) :
    Finset.sum s
      (fun j =>
        if M < blockDistance j ℓ then
          C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2)
        else 0) ≤
      localizationLeakageCoefficient C c B d M := by
  let t : Finset ℕ := s.image (fun j => blockDistance j ℓ)
  have hmaps : ∀ j ∈ s, blockDistance j ℓ ∈ t := by
    intro j hj
    exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
  have hdecomp := Finset.sum_fiberwise_of_maps_to (s := s) (t := t)
    (g := fun j : MultiIndex d => blockDistance j ℓ)
    (h := hmaps)
    (f := fun j : MultiIndex d =>
      if M < blockDistance j ℓ then
        C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2)
      else 0)
  dsimp [t] at hdecomp
  rw [← hdecomp]
  have hfiber :
      ∀ r ∈ s.image (fun j => blockDistance j ℓ),
        Finset.sum (s.filter fun j => blockDistance j ℓ = r)
          (fun j =>
            if M < blockDistance j ℓ then
              C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2)
            else 0) =
          (((s.filter fun j => blockDistance j ℓ = r).card : ℕ) : ℝ) *
            (if M < r then C * Real.exp (-(c) * max ((r : ℝ) - B) 0 ^ 2) else 0) := by
    intro r hr
    calc
      Finset.sum (s.filter fun j => blockDistance j ℓ = r)
        (fun j =>
          if M < blockDistance j ℓ then
            C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2)
          else 0)
        =
          Finset.sum (s.filter fun j => blockDistance j ℓ = r)
            (fun _ =>
              if M < r then C * Real.exp (-(c) * max ((r : ℝ) - B) 0 ^ 2) else 0) := by
              refine Finset.sum_congr rfl ?_
              simp_all
      _ =
          (((s.filter fun j => blockDistance j ℓ = r).card : ℕ) : ℝ) *
            (if M < r then C * Real.exp (-(c) * max ((r : ℝ) - B) 0 ^ 2) else 0) := by
              rw [Finset.sum_const, nsmul_eq_mul]
  calc
    Finset.sum (s.image (fun j => blockDistance j ℓ))
      (fun r =>
        Finset.sum (s.filter fun j => blockDistance j ℓ = r)
          (fun j =>
            if M < blockDistance j ℓ then
              C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2)
            else 0))
      ≤
        Finset.sum (s.image (fun j => blockDistance j ℓ))
          (fun r =>
            (shellCardinality d r : ℝ) *
              (if M < r then C * Real.exp (-(c) * max ((r : ℝ) - B) 0 ^ 2) else 0)) := by
          refine Finset.sum_le_sum fun r hr => ?_
          rw [hfiber r hr]
          by_cases hMr : M < r
          · have hr1 : 1 ≤ r := by omega
            have hker_nonneg : 0 ≤ C * Real.exp (-(c) * max ((r : ℝ) - B) 0 ^ 2) := by positivity
            simp only [hMr, ite_true]
            exact mul_le_mul_of_nonneg_right (hcard ℓ r s hr1) hker_nonneg
          · simp [hMr]
    _ ≤ localizationLeakageCoefficient C c B d M :=
          htail M (s.image (fun j => blockDistance j ℓ))
end Hermite1DimdLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
open Hermite1DimdLEAN
namespace Hermite1DimdLEAN
theorem _root_.solution
    {d : ℕ} (κ : MultiIndex d) :
    ∃ C c B : ℝ, 0 < C ∧ 0 < c ∧ 0 ≤ B ∧
      Filter.Tendsto
        (fun M : ℕ => localizationLeakageCoefficient C c B d M)
        Filter.atTop (nhds 0) ∧
      ∀ (s : Finset (MultiIndex d)) (M : ℕ) (G : FiniteHermiteSum d),
        ∑ j ∈ s, annulusMass j (evalHermiteSum κ (remainderPart j M G)) ≤
          localizationLeakageCoefficient C c B d M * hermiteNormSq κ G := by
  obtain ⟨C, c, B, hCpos, hcpos, hBnonneg, hloc⟩ := blockLocalization (κ := κ)
  refine ⟨C, c, B, hCpos, hcpos, hBnonneg, ?_, ?_⟩
  · exact localizationLeakageCoefficient_tendsto_zero (d := d) hCpos hcpos hBnonneg
  · intro s M G
    exact finitePartialLeakage_bound_of_shell_sum_bound
      (κ := κ) (hC := le_of_lt hCpos) hloc
      (shell_sum_bound_of_shell_cardinality_bound
        (d := d) (C := C) (c := c) (B := B) (le_of_lt hCpos)
        (shell_sum_localizationLeakageCoefficient_bound (d := d) hCpos hcpos hBnonneg)
        (fun ℓ r s hr => shell_cardinality_bound_filter ℓ r s hr))
      s M G
end Hermite1DimdLEAN

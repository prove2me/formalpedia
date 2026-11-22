-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.Hamming.lem_3_3_proof
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:48:36.315794+00:00
-- url     : https://prove2.me/submissions/d293979f-9a8b-4ce5-a29e-56ccb540731b

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Definitions.Def_LeanPool_SteinerSpanners_Defs
public import Definitions.Def_LeanPool_SteinerSpanners_Geometry
public import Definitions.Def_LeanPool_SteinerSpanners_Hamming
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_Geometry_lpDist_eq_toLp_dist

section
@[expose] public section
open scoped ENNReal
open HighDimSteinerSpanners
namespace HighDimSteinerSpanners.Proofs.Hamming
private lemma cubeLpDist_nonneg {p : ℝ} (hp : 1 ≤ p) {d : ℕ} (x y : Fin d → Bool) :
    0 ≤ cubeLpDist p x y := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  unfold cubeLpDist
  rw [Geometry.lpDist_eq_toLp_dist p hp]
  exact dist_nonneg
private lemma cubeLpDist_self {p : ℝ} (hp : 1 ≤ p) {d : ℕ} (x : Fin d → Bool) :
    cubeLpDist p x x = 0 := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  unfold cubeLpDist
  rw [Geometry.lpDist_eq_toLp_dist p hp]
  exact dist_self _
private lemma cubeLpDist_triangle {p : ℝ} (hp : 1 ≤ p) {d : ℕ} (x y z : Fin d → Bool) :
    cubeLpDist p x z ≤ cubeLpDist p x y + cubeLpDist p y z := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  unfold cubeLpDist
  rw [Geometry.lpDist_eq_toLp_dist p hp, Geometry.lpDist_eq_toLp_dist p hp,
    Geometry.lpDist_eq_toLp_dist p hp]
  exact dist_triangle _ _ _
private lemma cubeLpDist_eq_hamming_rpow {p : ℝ} (hp : 1 ≤ p) {d : ℕ} (x y : Fin d → Bool) :
    cubeLpDist p x y = (hammingDist x y : ℝ) ^ (1 / p) := by
  have hp0 : p ≠ 0 := by linarith
  unfold cubeLpDist lpDist
  congr 1
  have hterm : ∀ i : Fin d,
      |boolVecToReal x i - boolVecToReal y i| ^ p = if x i ≠ y i then 1 else 0 := by
    intro i
    unfold boolVecToReal
    cases hx : x i <;> cases hy : y i <;> simp [Real.zero_rpow hp0]
  simp_rw [hterm]
  rw [Finset.sum_boole]
  rfl
private lemma cubeLpDist_le_of_hamming_le {p C : ℝ} (hp : 1 ≤ p) (hC : 1 ≤ C) {d : ℕ}
    (u v x y : Fin d → Bool) (h : (hammingDist u v : ℝ) ≤ C * (hammingDist x y : ℝ)) :
    cubeLpDist p u v ≤ C * cubeLpDist p x y := by
  rw [cubeLpDist_eq_hamming_rpow hp u v, cubeLpDist_eq_hamming_rpow hp x y]
  have hp_inv_nonneg : 0 ≤ 1 / p := by positivity
  have hp_inv_le_one : 1 / p ≤ 1 := div_le_one_of_le₀ hp (by positivity)
  calc
    (hammingDist u v : ℝ) ^ (1 / p)
        ≤ (C * (hammingDist x y : ℝ)) ^ (1 / p) :=
          Real.rpow_le_rpow (by positivity) h hp_inv_nonneg
    _ = C ^ (1 / p) * (hammingDist x y : ℝ) ^ (1 / p) :=
          Real.mul_rpow (by linarith) (by positivity)
    _ ≤ C ^ (1 : ℝ) * (hammingDist x y : ℝ) ^ (1 / p) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hC hp_inv_le_one) (by
              positivity)
    _ = C * (hammingDist x y : ℝ) ^ (1 / p) := by rw [Real.rpow_one]
private lemma cubeSubgraphWeight_mk (p : ℝ) {d : ℕ} (V : Finset (Fin d → Bool)) (a b : ↥V) :
    cubeSubgraphWeight p V s(a, b) = cubeLpDist p a.val b.val := by
  simp [cubeSubgraphWeight]
private lemma graphDist_noncontracting {V : Type} {d : ℕ} {p : ℝ} (hp : 1 ≤ p)
    (emb : V → (Fin d → Bool)) (H : SimpleGraph V) (w : Sym2 V → ℝ)
    (hw : ∀ a b : V, w s(a, b) = cubeLpDist p (emb a) (emb b)) (u v : V) :
    ENNReal.ofReal (cubeLpDist p (emb u) (emb v)) ≤ graphDist H w u v := by
  have hwalk : ∀ {a b : V} (q : H.Walk a b), cubeLpDist p (emb a) (emb b) ≤ walkWeight w q := by
    intro a b q
    induction q with
    | nil => simp [walkWeight, cubeLpDist_self hp]
    | @cons a m b _ q' ih =>
      have htri := cubeLpDist_triangle hp (emb a) (emb m) (emb b)
      simp only [walkWeight, hw a m]
      linarith
  exact le_iInf (fun q => ENNReal.ofReal_le_ofReal (hwalk q))
private lemma cubeSubgraph_noncontracting {d : ℕ} {p : ℝ} (hp : 1 ≤ p)
    (P S : Finset (Fin d → Bool)) (H : SimpleGraph ↥(P ∪ S))
    (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P) :
    ENNReal.ofReal (cubeLpDist p x y) ≤
      graphDist H (cubeSubgraphWeight p (P ∪ S))
        ⟨x, Finset.mem_union_left S hx⟩ ⟨y, Finset.mem_union_left S hy⟩ :=
  graphDist_noncontracting hp Subtype.val H (cubeSubgraphWeight p (P ∪ S))
    (cubeSubgraphWeight_mk p (P ∪ S))
    ⟨x, Finset.mem_union_left S hx⟩ ⟨y, Finset.mem_union_left S hy⟩
private lemma exists_path_le_three {V : Type} (H : SimpleGraph V) (w : Sym2 V → ℝ)
    (hw_nonneg : ∀ a b : V, 0 ≤ w s(a, b))
    (v₀ v₁ v₂ v₃ : V) (h03 : v₀ ≠ v₃)
    (h01 : v₀ ≠ v₁ → H.Adj v₀ v₁)
    (h12 : v₁ ≠ v₂ → H.Adj v₁ v₂)
    (h23 : v₂ ≠ v₃ → H.Adj v₂ v₃) :
    ∃ q : H.Walk v₀ v₃,
      q.IsPath ∧ q.length ≤ 3 ∧
      walkWeight w q ≤ w s(v₀, v₁) + w s(v₁, v₂) + w s(v₂, v₃) := by
  have hw01 := hw_nonneg v₀ v₁
  have hw12 := hw_nonneg v₁ v₂
  have hw23 := hw_nonneg v₂ v₃
  by_cases heq02 : v₀ = v₂
  · subst heq02
    have hadj := h23 h03
    refine ⟨.cons hadj .nil, ?_, by simp, ?_⟩
    · rw [SimpleGraph.Walk.isPath_def]; simp [h03]
    · simp only [walkWeight]; linarith
  · by_cases heq13 : v₁ = v₃
    · subst heq13
      have hadj := h01 h03
      refine ⟨.cons hadj .nil, ?_, by simp, ?_⟩
      · rw [SimpleGraph.Walk.isPath_def]; simp [h03]
      · simp only [walkWeight]; linarith
    · by_cases heq01 : v₀ = v₁
      · subst heq01
        by_cases heq23 : v₂ = v₃
        · subst heq23
          have hadj := h12 h03
          refine ⟨.cons hadj .nil, ?_, by simp, ?_⟩
          · rw [SimpleGraph.Walk.isPath_def]; simp [h03]
          · simp only [walkWeight]; linarith
        · refine ⟨.cons (h12 heq02) (.cons (h23 heq23) .nil), ?_, by simp, ?_⟩
          · rw [SimpleGraph.Walk.isPath_def]; simp [heq02, h03, heq23]
          · simp only [walkWeight]; linarith
      · by_cases heq23 : v₂ = v₃
        · subst heq23
          refine ⟨.cons (h01 heq01) (.cons (h12 heq13) .nil), ?_, by simp, ?_⟩
          · rw [SimpleGraph.Walk.isPath_def]; simp [heq01, h03, heq13]
          · simp only [walkWeight]; linarith
        · by_cases heq12 : v₁ = v₂
          · subst heq12
            refine ⟨.cons (h01 heq01) (.cons (h23 heq13) .nil), ?_, by simp, ?_⟩
            · rw [SimpleGraph.Walk.isPath_def]; simp [heq01, h03, heq13]
            · simp only [walkWeight]; linarith
          · refine ⟨.cons (h01 heq01) (.cons (h12 heq12) (.cons (h23 heq23) .nil)), ?_, by simp, ?_⟩
            · rw [SimpleGraph.Walk.isPath_def]
              simp [heq01, heq02, h03, heq12, heq13, heq23]
            · simp only [walkWeight]; linarith
private lemma card_edgeSet_le_finset {V : Type} (H : SimpleGraph V) (E₀ : Finset (Sym2 V))
    (hsub : ∀ u v : V, H.Adj u v → s(u, v) ∈ E₀) :
    Nat.card H.edgeSet ≤ E₀.card := by
  have hmem : ∀ e : H.edgeSet, e.1 ∈ E₀ := by
    rintro ⟨e, he⟩
    refine Sym2.ind (fun u v huv => hsub u v ?_) e he
    exact H.mem_edgeSet.mp huv
  let f : H.edgeSet → ↥E₀ := fun e => ⟨e.1, hmem e⟩
  have hf_inj : Function.Injective f := fun e₁ e₂ h => Subtype.ext (Subtype.mk.inj h)
  calc
    Nat.card H.edgeSet ≤ Nat.card ↥E₀ := Nat.card_le_card_of_injective f hf_inj
    _ = E₀.card := (Nat.card_eq_fintype_card).trans (Fintype.card_coe E₀)
private lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide
private lemma vec_zmod2_add_self {r : ℕ} (v : Fin r → ZMod 2) : v + v = 0 := by
  ext i; exact zmod2_add_self (v i)
private lemma flipBit_involutive {n : ℕ} (u : Fin n → Bool) (j : Fin n) :
    flipBit (flipBit u j) j = u := by
  ext i
  unfold flipBit
  by_cases h : i = j
  · subst h; simp
  · simp [h]
private lemma hammingDist_flipBit {n : ℕ} (u : Fin n → Bool) (j : Fin n) :
    hammingDist u (flipBit u j) = 1 := by
  have heq : (Finset.univ.filter (fun i : Fin n => u i ≠ flipBit u j i)) = {j} := by
    apply Finset.ext
    intro i
    rw [Finset.mem_filter, Finset.mem_singleton]
    simp only [Finset.mem_univ, true_and]
    by_cases h : i = j
    · subst h; simp [flipBit]
    · simp [flipBit, h]
  exact (Finset.card_singleton j) ▸ congrArg Finset.card heq
private lemma hammingSyndrome_flipBit (r : ℕ) (u : Fin (2 ^ r - 1) → Bool)
    (j₀ : Fin (2 ^ r - 1)) :
    hammingSyndrome r (flipBit u j₀) = hammingSyndrome r u + (hammingColEquiv r j₀).val := by
  unfold hammingSyndrome
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ j₀)]
  have hrest : ∑ j ∈ Finset.univ.erase j₀,
      (if flipBit u j₀ j then (hammingColEquiv r j).val else 0) =
      ∑ j ∈ Finset.univ.erase j₀, (if u j then (hammingColEquiv r j).val else 0) := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hne : j ≠ j₀ := Finset.ne_of_mem_erase hj
    simp [flipBit, hne]
  rw [hrest]
  have hj₀ : (if flipBit u j₀ j₀ then (hammingColEquiv r j₀).val else 0) =
      (if u j₀ then (hammingColEquiv r j₀).val else 0) + (hammingColEquiv r j₀).val := by
    simp only [flipBit, Function.update_self]
    cases u j₀
    · simp
    · simp [vec_zmod2_add_self]
  rw [hj₀]
  abel
private lemma hammingBlkDecode_mem (r : ℕ) (u : Fin (2 ^ r - 1) → Bool) :
    hammingBlkDecode r u ∈ hammingBlkCode r := by
  unfold hammingBlkCode hammingBlkDecode
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs with h
  · exact h
  · rw [hammingSyndrome_flipBit, Equiv.apply_symm_apply]
    exact vec_zmod2_add_self _
private lemma hammingDist_hammingBlkDecode_le_one (r : ℕ) (u : Fin (2 ^ r - 1) → Bool) :
    hammingDist u (hammingBlkDecode r u) ≤ 1 := by
  unfold hammingBlkDecode
  split_ifs with h
  · simp
  · rw [hammingDist_flipBit]
private lemma card_hammingBlkCode (r : ℕ) :
    (hammingBlkCode r).card = 2 ^ ((2 ^ r - 1) - r) := by
  let bNat := 2 ^ r - 1
  let toVec : ↥(hammingBlkCode r) × Option (Fin bNat) → (Fin bNat → Bool) :=
    fun p => match p.2 with
      | none => p.1.val
      | some j => flipBit p.1.val j
  let fromVec : (Fin bNat → Bool) → ↥(hammingBlkCode r) × Option (Fin bNat) :=
    fun u =>
      if h : hammingSyndrome r u = 0 then
        (⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩, none)
      else
        let j := (hammingColEquiv r).symm ⟨hammingSyndrome r u,
          Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩⟩
        (⟨flipBit u j, by
          rw [hammingBlkCode, Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          rw [hammingSyndrome_flipBit, Equiv.apply_symm_apply]
          exact vec_zmod2_add_self _⟩, some j)
  have hleft : Function.LeftInverse fromVec toVec := by
    rintro ⟨⟨z, hz⟩, opt⟩
    have hz0 : hammingSyndrome r z = 0 := (Finset.mem_filter.mp hz).2
    cases opt with
    | none =>
      dsimp [toVec, fromVec]
      rw [dif_pos hz0]
    | some j =>
      dsimp [toVec, fromVec]
      have hsyn : hammingSyndrome r (flipBit z j) = (hammingColEquiv r j).val := by
        rw [hammingSyndrome_flipBit, hz0, zero_add]
      have hne : hammingSyndrome r (flipBit z j) ≠ 0 := by
        rw [hsyn]
        exact (Finset.mem_erase.mp (hammingColEquiv r j).prop).1
      rw [dif_neg hne]
      have hj : (hammingColEquiv r).symm ⟨hammingSyndrome r (flipBit z j),
          Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩⟩ = j := by
        have hsub : (⟨hammingSyndrome r (flipBit z j),
            Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩⟩ :
            ↥(Finset.univ.erase (0 : Fin r → ZMod 2))) = hammingColEquiv r j :=
          Subtype.ext hsyn
        rw [hsub, Equiv.symm_apply_apply]
      ext1
      · apply Subtype.ext
        dsimp
        rw [hj, flipBit_involutive]
      · dsimp
        rw [hj]
  have hright : Function.RightInverse fromVec toVec := by
    intro u
    dsimp [fromVec]
    split_ifs with h
    · rfl
    · dsimp [toVec]
      exact flipBit_involutive u _
  let e : (↥(hammingBlkCode r) × Option (Fin bNat)) ≃ (Fin bNat → Bool) :=
    ⟨toVec, fromVec, hleft, hright⟩
  have hcard := Fintype.card_congr e
  rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_option, Fintype.card_fin,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hcard
  have hpow_ge1 : 1 ≤ 2 ^ r := Nat.one_le_pow r 2 (by norm_num)
  have hb_succ : bNat + 1 = 2 ^ r := Nat.sub_add_cancel hpow_ge1
  rw [hb_succ] at hcard
  have hr_le_b : r ≤ bNat := by
    dsimp [bNat]
    have hlt : r < 2 ^ r := r.lt_two_pow_self
    omega
  have hsplit : 2 ^ bNat = 2 ^ (bNat - r) * 2 ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hr_le_b]
  rw [hsplit] at hcard
  exact Nat.eq_of_mul_eq_mul_right (by positivity) hcard
private lemma getBlock_mkFromBlocks (r d : ℕ)
    (B : Fin (d / (2 ^ r - 1)) → Fin (2 ^ r - 1) → Bool)
    (R : Fin (d % (2 ^ r - 1)) → Bool) (m : Fin (d / (2 ^ r - 1))) :
    getBlock r d (mkFromBlocks r d B R) m = B m := by
  ext j
  simp [getBlock, mkFromBlocks]
private lemma getRem_mkFromBlocks (r d : ℕ)
    (B : Fin (d / (2 ^ r - 1)) → Fin (2 ^ r - 1) → Bool)
    (R : Fin (d % (2 ^ r - 1)) → Bool) :
    getRem r d (mkFromBlocks r d B R) = R := by
  ext k
  simp [getRem, mkFromBlocks]
private lemma mkFromBlocks_get (r d : ℕ) (x : Fin d → Bool) :
    mkFromBlocks r d (getBlock r d x) (getRem r d x) = x := by
  ext i
  unfold mkFromBlocks
  rcases h : (coordEquiv r d).symm i with ⟨m, j⟩ | k
  · simp only [getBlock]
    have hi : coordEquiv r d (.inl (m, j)) = i := (coordEquiv r d).eq_symm_apply.mp h.symm
    rw [hi]
  · simp only [getRem]
    have hi : coordEquiv r d (.inr k) = i := (coordEquiv r d).eq_symm_apply.mp h.symm
    rw [hi]
private lemma hammingDist_eq_sum_boole {n : ℕ} (u v : Fin n → Bool) :
    hammingDist u v = ∑ i : Fin n, if u i ≠ v i then 1 else 0 := by
  change (Finset.univ.filter (fun i : Fin n => u i ≠ v i)).card = _
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
private lemma hammingDist_block_decomp (r d : ℕ) (x y : Fin d → Bool) :
    hammingDist x y =
      (∑ m : Fin (d / (2 ^ r - 1)), hammingDist (getBlock r d x m) (getBlock r d y m)) +
      hammingDist (getRem r d x) (getRem r d y) := by
  rw [hammingDist_eq_sum_boole x y, ← (coordEquiv r d).sum_comp]
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  congr 1
  · refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [hammingDist_eq_sum_boole]
    rfl
  · rw [hammingDist_eq_sum_boole]
    rfl
private lemma blockDecode_mem (r d : ℕ) (x : Fin d → Bool) :
    blockDecode r d x ∈ blockCode r d := by
  unfold blockCode blockDecode
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, getBlock_mkFromBlocks]
  intro m
  exact hammingBlkDecode_mem r _
private lemma card_blockCode (r d : ℕ) :
    (blockCode r d).card = 2 ^ (d - (d / (2 ^ r - 1)) * r) := by
  let M := d / (2 ^ r - 1)
  let q₀ := d % (2 ^ r - 1)
  let toPair : ↥(blockCode r d) → (Fin M → ↥(hammingBlkCode r)) × (Fin q₀ → Bool) :=
    fun c => (fun m => ⟨getBlock r d c.val m, (Finset.mem_filter.mp c.prop).2 m⟩, getRem r d c.val)
  let fromPair : (Fin M → ↥(hammingBlkCode r)) × (Fin q₀ → Bool) → ↥(blockCode r d) :=
    fun p => ⟨mkFromBlocks r d (fun m => (p.1 m).val) p.2, by
      rw [blockCode, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun m => ?_⟩
      rw [getBlock_mkFromBlocks]
      exact (p.1 m).prop⟩
  have hleft : Function.LeftInverse fromPair toPair := by
    intro c
    apply Subtype.ext
    dsimp [toPair, fromPair]
    exact mkFromBlocks_get r d c.val
  have hright : Function.RightInverse fromPair toPair := by
    rintro ⟨B, R⟩
    ext1
    · ext m j
      dsimp [toPair, fromPair]
      rw [getBlock_mkFromBlocks]
    · dsimp [toPair, fromPair]
      rw [getRem_mkFromBlocks]
  let e : ↥(blockCode r d) ≃ (Fin M → ↥(hammingBlkCode r)) × (Fin q₀ → Bool) :=
    ⟨toPair, fromPair, hleft, hright⟩
  have hcard := Fintype.card_congr e
  rw [Fintype.card_coe, Fintype.card_prod, Fintype.card_fun, Fintype.card_coe,
    Fintype.card_fin, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    card_hammingBlkCode r] at hcard
  have hr_le : r ≤ 2 ^ r - 1 := by
    have hlt : r < 2 ^ r := r.lt_two_pow_self
    omega
  have hdiv : (2 ^ r - 1) * M + q₀ = d := Nat.div_add_mod d (2 ^ r - 1)
  have hexp : ((2 ^ r - 1 - r) * M + q₀) = d - M * r := by
    rw [Nat.sub_mul, Nat.mul_comm r M]
    have hle1 : M * r ≤ (2 ^ r - 1) * M := by
      rw [Nat.mul_comm M r]
      exact Nat.mul_le_mul_right M hr_le
    omega
  calc
    (blockCode r d).card = (2 ^ (2 ^ r - 1 - r)) ^ M * 2 ^ q₀ := hcard
    _ = 2 ^ ((2 ^ r - 1 - r) * M + q₀) := by rw [← pow_mul, ← pow_add]
    _ = 2 ^ (d - M * r) := by rw [hexp]
private lemma hammingDist_blockDecode_le (r d : ℕ) (x : Fin d → Bool) :
    hammingDist x (blockDecode r d x) ≤ d / (2 ^ r - 1) := by
  rw [hammingDist_block_decomp r d x (blockDecode r d x)]
  unfold blockDecode
  simp only [getBlock_mkFromBlocks, getRem_mkFromBlocks, hammingDist_self, add_zero]
  calc
    ∑ m : Fin (d / (2 ^ r - 1)), hammingDist (getBlock r d x m) (hammingBlkDecode r (getBlock r
        d x m))
        ≤ ∑ _m : Fin (d / (2 ^ r - 1)), 1 :=
          Finset.sum_le_sum (fun m _ => hammingDist_hammingBlkDecode_le_one r _)
    _ = d / (2 ^ r - 1) := by simp
private lemma hammingDist_blockDecode_pair_le (r d : ℕ) (x y : Fin d → Bool) :
    hammingDist (blockDecode r d x) (blockDecode r d y) ≤ 3 * hammingDist x y := by
  rw [hammingDist_block_decomp r d (blockDecode r d x) (blockDecode r d y),
      hammingDist_block_decomp r d x y]
  unfold blockDecode
  simp only [getBlock_mkFromBlocks, getRem_mkFromBlocks]
  have hblk : ∀ m : Fin (d / (2 ^ r - 1)),
      hammingDist (hammingBlkDecode r (getBlock r d x m)) (hammingBlkDecode r (getBlock r d y m)) ≤
      3 * hammingDist (getBlock r d x m) (getBlock r d y m) := by
    intro m
    set u := getBlock r d x m
    set v := getBlock r d y m
    by_cases huv : u = v
    · rw [huv, hammingDist_self]; omega
    · have hpos : 1 ≤ hammingDist u v := Nat.succ_le_of_lt (hammingDist_pos.mpr huv)
      have htri1 := hammingDist_triangle (hammingBlkDecode r u) u (hammingBlkDecode r v)
      have htri2 := hammingDist_triangle u v (hammingBlkDecode r v)
      have hu : hammingDist (hammingBlkDecode r u) u ≤ 1 := by
        rw [hammingDist_comm]; exact hammingDist_hammingBlkDecode_le_one r u
      have hv : hammingDist v (hammingBlkDecode r v) ≤ 1 :=
        hammingDist_hammingBlkDecode_le_one r v
      omega
  have hsum : ∑ m : Fin (d / (2 ^ r - 1)),
      hammingDist (hammingBlkDecode r (getBlock r d x m)) (hammingBlkDecode r (getBlock r d y m)) ≤
      3 * ∑ m : Fin (d / (2 ^ r - 1)), hammingDist (getBlock r d x m) (getBlock r d y m) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun m _ => hblk m)
  omega
private lemma card_hamming_sphere_bool (d : ℕ) (c : Fin d → Bool) (j : ℕ) :
    (Finset.univ.filter (fun c' : Fin d → Bool => hammingDist c c' = j)).card = d.choose j := by
  have hbij : (Finset.univ.filter (fun c' : Fin d → Bool => hammingDist c c' = j)).card =
      ((Finset.univ : Finset (Fin d)).powersetCard j).card := by
    refine Finset.card_bij (fun c' _ => Finset.univ.filter (fun i : Fin d => c i ≠ c' i)) ?_ ?_ ?_
    · intro c' hc'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc'
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, hc'⟩
    · intro c₁ _ c₂ _ heq
      ext i
      have hmem := Finset.ext_iff.mp heq i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      cases hc : c i <;> cases hc1 : c₁ i <;> cases hc2 : c₂ i <;> simp_all
    · intro S hS
      rw [Finset.mem_powersetCard] at hS
      let c' : Fin d → Bool := fun i => if i ∈ S then !c i else c i
      have hdiff : Finset.univ.filter (fun i : Fin d => c i ≠ c' i) = S := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, c']
        by_cases hi : i ∈ S <;> cases c i <;> simp [hi]
      refine ⟨c', ?_, hdiff⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change (Finset.univ.filter (fun i : Fin d => c i ≠ c' i)).card = j
      rw [hdiff, hS.2]
  rw [hbij, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
private lemma card_hamming_ball_pairs_le {d : ℕ} (C_sub : Finset (Fin d → Bool)) (k : ℕ) :
    ((C_sub ×ˢ C_sub).filter
      (fun cc' => 1 ≤ hammingDist cc'.1 cc'.2 ∧ hammingDist cc'.1 cc'.2 ≤ k)).card ≤
    C_sub.card * ∑ j ∈ Finset.Icc 1 k, d.choose j := by
  set pairs := (C_sub ×ˢ C_sub).filter
    (fun cc' => 1 ≤ hammingDist cc'.1 cc'.2 ∧ hammingDist cc'.1 cc'.2 ≤ k)
  have h_fib : ∀ c ∈ C_sub,
      (C_sub.filter (fun c' => 1 ≤ hammingDist c c' ∧ hammingDist c c' ≤ k)).card ≤
      ∑ j ∈ Finset.Icc 1 k, d.choose j := by
    intro c _
    have hsub : C_sub.filter (fun c' => 1 ≤ hammingDist c c' ∧ hammingDist c c' ≤ k) ⊆
        (Finset.Icc 1 k).biUnion
          (fun j => Finset.univ.filter (fun c' : Fin d → Bool => hammingDist c c' = j)) := by
      intro c' hc'
      simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_univ,
        true_and] at hc' ⊢
      exact ⟨hammingDist c c', hc'.2, rfl⟩
    calc
      (C_sub.filter (fun c' => 1 ≤ hammingDist c c' ∧ hammingDist c c' ≤ k)).card
          ≤ ((Finset.Icc 1 k).biUnion
              (fun j => Finset.univ.filter (fun c' : Fin d → Bool => hammingDist c c' = j))).card :=
            Finset.card_le_card hsub
      _ ≤ ∑ j ∈ Finset.Icc 1 k,
            (Finset.univ.filter (fun c' : Fin d → Bool => hammingDist c c' = j)).card :=
            Finset.card_biUnion_le
      _ = ∑ j ∈ Finset.Icc 1 k, d.choose j :=
            Finset.sum_congr rfl (fun j _ => card_hamming_sphere_bool d c j)
  have heq : pairs = C_sub.biUnion (fun c =>
      (C_sub.filter (fun c' => 1 ≤ hammingDist c c' ∧ hammingDist c c' ≤ k)).image (fun c' =>
          (c, c'))) := by
    ext ⟨c, c'⟩
    simp [pairs, and_assoc]
  rw [heq]
  calc
    (C_sub.biUnion _).card
        ≤ ∑ c ∈ C_sub, ((C_sub.filter (fun c' => 1 ≤ hammingDist c c' ∧ hammingDist c c' ≤ k)).image
            (fun c' => (c, c'))).card := Finset.card_biUnion_le
    _ ≤ ∑ c ∈ C_sub, (C_sub.filter (fun c' => 1 ≤ hammingDist c c' ∧ hammingDist c c' ≤ k)).card :=
          Finset.sum_le_sum (fun c _ => Finset.card_image_le)
    _ ≤ ∑ _c ∈ C_sub, (∑ j ∈ Finset.Icc 1 k, d.choose j) :=
          Finset.sum_le_sum h_fib
    _ = C_sub.card * ∑ j ∈ Finset.Icc 1 k, d.choose j := by simp
private lemma two_mul_sym2_image_le {d : ℕ} (V_set C_sub : Finset (Fin d → Bool))
    (hCV : C_sub ⊆ V_set) (k : ℕ) :
    let pairs := (C_sub ×ˢ C_sub).filter
      (fun cc' => 1 ≤ hammingDist cc'.1 cc'.2 ∧ hammingDist cc'.1 cc'.2 ≤ k)
    let toSym2 : ↥pairs → Sym2 ↥V_set := fun p =>
      s(⟨p.1.1, hCV (Finset.mem_product.mp (Finset.mem_filter.mp p.2).1).1⟩,
        ⟨p.1.2, hCV (Finset.mem_product.mp (Finset.mem_filter.mp p.2).1).2⟩)
    2 * (Finset.univ.image toSym2).card ≤ pairs.card := by
  intro pairs toSym2
  let E₂ := Finset.univ.image toSym2
  let fib : Sym2 ↥V_set → Finset ↥pairs := fun e =>
    Finset.univ.filter (fun p : ↥pairs => toSym2 p = e)
  have hdisj : (E₂ : Set (Sym2 ↥V_set)).PairwiseDisjoint fib := by
    intro e₁ _ e₂ _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro p hp₁ hp₂
    simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and] at hp₁ hp₂
    exact hne (hp₁.symm.trans hp₂)
  have htwo : ∀ e ∈ E₂, 2 ≤ (fib e).card := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨p, _, rfl⟩
    obtain ⟨⟨c, c'⟩, hp⟩ := p
    have hp_f := Finset.mem_filter.mp hp
    have hp_prod := Finset.mem_product.mp hp_f.1
    have hswap_mem : (c', c) ∈ pairs := by
      rw [Finset.mem_filter, Finset.mem_product]
      rw [hammingDist_comm]
      exact ⟨⟨hp_prod.2, hp_prod.1⟩, hp_f.2⟩
    let p₁ : ↥pairs := ⟨(c, c'), hp⟩
    let p₂ : ↥pairs := ⟨(c', c), hswap_mem⟩
    have hp_ne : p₁ ≠ p₂ := by
      intro heq
      have hcc : c = c' := (Prod.mk.inj (Subtype.mk.inj heq)).1
      have h1 := hp_f.2.1
      rw [hcc, hammingDist_self] at h1
      omega
    have hsub : ({p₁, p₂} : Finset ↥pairs) ⊆ fib (toSym2 p₁) := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hq with rfl | rfl
      · rfl
      · dsimp [toSym2, p₁, p₂]
        exact Sym2.eq_swap
    calc
      2 = ({p₁, p₂} : Finset ↥pairs).card := (Finset.card_pair hp_ne).symm
      _ ≤ (fib (toSym2 p₁)).card := Finset.card_le_card hsub
  calc
    2 * E₂.card = ∑ _e ∈ E₂, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ e ∈ E₂, (fib e).card := Finset.sum_le_sum htwo
    _ = (E₂.biUnion fib).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.univ : Finset ↥pairs).card := Finset.card_le_card (Finset.subset_univ _)
    _ = pairs.card := by rw [Finset.card_univ, Fintype.card_coe]
open Classical in
private lemma hamming_hsum_choose (r d : ℕ) (hr : 4 ≤ r) :
    let b_r : ℝ := (2 : ℝ) ^ r - 1;
    let ρ_r : ℝ := 1 / (64 * b_r);
    15 ≤ b_r →
      let k : ℕ := ⌊(27 / 4 : ℝ) * ρ_r * (d : ℝ)⌋₊;
      let α : ℝ := 7 * ρ_r;
      0 < α → α < 1 → (k : ℝ) ≤ α * (d : ℝ) → k < d →
        ∑ j ∈ Finset.Icc 1 k, (d.choose j : ℝ) ≤
          (2 : ℝ) ^ ((r : ℝ) / (4 * b_r) * (d : ℝ)) := by
  classical
  intro b_r ρ_r hbr_ge15 k α hα_pos hα_lt1 hk_le_αd hk_lt_d
  have hsub_range : Finset.Icc 1 k ⊆ Finset.range (d + 1) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    rw [Finset.mem_range]
    omega
  have hmul_αk : (∑ j ∈ Finset.Icc 1 k, (d.choose j : ℝ)) * α ^ k ≤ (α + 1) ^ d := by
    calc
      (∑ j ∈ Finset.Icc 1 k, (d.choose j : ℝ)) * α ^ k
          = ∑ j ∈ Finset.Icc 1 k, (d.choose j : ℝ) * α ^ k := Finset.sum_mul _ _ _
      _ ≤ ∑ j ∈ Finset.Icc 1 k, (d.choose j : ℝ) * α ^ j := by
            refine Finset.sum_le_sum (fun j hj => ?_)
            rw [Finset.mem_Icc] at hj
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_of_le_one hα_pos.le hα_lt1.le hj.2) (by positivity)
      _ ≤ ∑ j ∈ Finset.range (d + 1), (d.choose j : ℝ) * α ^ j :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub_range (fun _ _ _ => by positivity)
      _ = (α + 1) ^ d := by
            rw [add_pow]
            refine Finset.sum_congr rfl (fun j _ => by ring)
  have hexp_d : (α + 1) ^ d ≤ (Real.exp 1) ^ (α * (d : ℝ)) := by
    calc
      (α + 1) ^ d ≤ (Real.exp α) ^ d :=
        pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp α) d
      _ = Real.exp ((d : ℝ) * α) := (Real.exp_nat_mul α d).symm
      _ = (Real.exp 1) ^ (α * (d : ℝ)) := by
        rw [Real.rpow_def_of_pos (Real.exp_pos 1), Real.log_exp, one_mul, mul_comm]
  have hdiv_αk : (∑ j ∈ Finset.Icc 1 k, (d.choose j : ℝ)) ≤
      (Real.exp 1) ^ (α * (d : ℝ)) * (1 / α) ^ k := by
    have h1 : (∑ j ∈ Finset.Icc 1 k, (d.choose j : ℝ)) * α ^ k ≤
        (Real.exp 1) ^ (α * (d : ℝ)) := le_trans hmul_αk hexp_d
    rw [← le_div_iff₀ (pow_pos hα_pos k)] at h1
    simpa [div_eq_mul_inv, one_div, inv_pow] using h1
  have h1_le_invα : 1 ≤ 1 / α := one_le_one_div hα_pos hα_lt1.le
  have hpow_k : ((1 / α) ^ k : ℝ) ≤ (1 / α) ^ (α * (d : ℝ)) := by
    rw [← Real.rpow_natCast (1 / α) k]
    exact Real.rpow_le_rpow_of_exponent_le h1_le_invα hk_le_αd
  have hbase_le : Real.exp 1 * (1 / α) ≤ (2 : ℝ) ^ ((9 / 4 : ℝ) * (r : ℝ)) := by
    have hexp_lt : Real.exp 1 < 2.72 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have hinvα_eq : 1 / α = 64 / 7 * b_r := by
      dsimp [α, ρ_r]
      field_simp
    have hbr_lt : b_r < (2 : ℝ) ^ (r : ℝ) := by
      dsimp [b_r]
      rw [Real.rpow_natCast]
      linarith
    have hprod_lt : Real.exp 1 * (1 / α) ≤ (2 : ℝ) ^ (5 : ℝ) * (2 : ℝ) ^ (r : ℝ) := by
      rw [hinvα_eq]
      have h32 : (2 : ℝ) ^ (5 : ℝ) = 32 := by norm_num
      rw [h32]
      have h2r_pos : (0 : ℝ) < (2 : ℝ) ^ (r : ℝ) := by positivity
      nlinarith
    have hr_ge4 : (4 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    calc
      Real.exp 1 * (1 / α)
          ≤ (2 : ℝ) ^ (5 : ℝ) * (2 : ℝ) ^ (r : ℝ) := hprod_lt
      _ = (2 : ℝ) ^ ((5 : ℝ) + (r : ℝ)) := (Real.rpow_add (by norm_num) 5 (r : ℝ)).symm
      _ ≤ (2 : ℝ) ^ ((9 / 4 : ℝ) * (r : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hexp_prod_le : ((9 / 4 : ℝ) * (r : ℝ)) * (α * (d : ℝ)) ≤
      (r : ℝ) / (4 * b_r) * (d : ℝ) := by
    dsimp [α, ρ_r]
    have hr_nn : (0 : ℝ) ≤ (r : ℝ) := by positivity
    have h_eq1 : ((9 / 4 : ℝ) * (r : ℝ)) * (7 * (1 / (64 * b_r)) * (d : ℝ)) =
        (63 / 256 : ℝ) * ((r : ℝ) / b_r * (d : ℝ)) := by ring_nf
    have h_eq2 : (r : ℝ) / (4 * b_r) * (d : ℝ) =
        (64 / 256 : ℝ) * ((r : ℝ) / b_r * (d : ℝ)) := by ring_nf
    rw [h_eq1, h_eq2]
    have hpos_term : 0 ≤ (r : ℝ) / b_r * (d : ℝ) := by positivity
    linarith
  calc
    (∑ j ∈ Finset.Icc 1 k, (d.choose j : ℝ))
        ≤ (Real.exp 1) ^ (α * (d : ℝ)) * (1 / α) ^ k := hdiv_αk
    _ ≤ (Real.exp 1) ^ (α * (d : ℝ)) * (1 / α) ^ (α * (d : ℝ)) :=
          mul_le_mul_of_nonneg_left hpow_k (by positivity)
    _ = (Real.exp 1 * (1 / α)) ^ (α * (d : ℝ)) :=
          (Real.mul_rpow (Real.exp_pos 1).le (by positivity)).symm
    _ ≤ ((2 : ℝ) ^ ((9 / 4 : ℝ) * (r : ℝ))) ^ (α * (d : ℝ)) :=
          Real.rpow_le_rpow (by positivity) hbase_le (by positivity)
    _ = (2 : ℝ) ^ (((9 / 4 : ℝ) * (r : ℝ)) * (α * (d : ℝ))) :=
          (Real.rpow_mul (by norm_num) _ _).symm
    _ ≤ (2 : ℝ) ^ ((r : ℝ) / (4 * b_r) * (d : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_prod_le
open Classical in
private lemma blockCode_closePair_cardinality_bound (r d k : ℕ)
    (P : Finset (Fin d → Bool)) (hr : 0 < r) :
    let b_r : ℝ := (2 : ℝ) ^ r - 1;
    0 < b_r → 28 * b_r < (d : ℝ) →
    (2 : ℝ) ^ ((1 - (r : ℝ) / (2 * b_r)) * (d : ℝ)) ≤ (P.card : ℝ) →
    (∑ j ∈ Finset.Icc 1 k, (d.choose j : ℝ)) ≤
      (2 : ℝ) ^ ((r : ℝ) / (4 * b_r) * (d : ℝ)) →
    let C_r := blockCode r d;
    let pairs_C := {cc' ∈ C_r ×ˢ C_r | 1 ≤ hammingDist cc'.1 cc'.2 ∧
      hammingDist cc'.1 cc'.2 ≤ k};
    (pairs_C.card : ℝ) ≤ 2 * (P.card : ℝ) := by
  classical
  intro b_r hbr_pos hd_gt_28b hP_rate hsum_choose C_r pairs_C
  let bNat : ℕ := 2 ^ r - 1
  have hbNat_cast : (bNat : ℝ) = b_r := by
    dsimp [bNat, b_r]
    rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  have hbNat_pos : 0 < bNat := by
    exact_mod_cast (show (0 : ℝ) < (bNat : ℝ) by rwa [hbNat_cast])
  let M := d / bNat
  have hcard_Cr : (C_r.card : ℝ) = (2 : ℝ) ^ ((d - M * r : ℕ) : ℝ) := by
    have hc := card_blockCode r d
    change (C_r.card : ℝ) = _
    rw [hc, Real.rpow_natCast]
    push_cast
    rfl
  have hr_le_bNat : r ≤ bNat := by
    dsimp [bNat]
    have hlt : r < 2 ^ r := r.lt_two_pow_self
    omega
  have hMr_le_d : M * r ≤ d :=
    le_trans (Nat.mul_le_mul_left M hr_le_bNat) (Nat.div_mul_le_self d bNat)
  have hsub_cast : ((d - M * r : ℕ) : ℝ) = (d : ℝ) - (M : ℝ) * (r : ℝ) := by
    rw [Nat.cast_sub hMr_le_d, Nat.cast_mul]
  have hM_gt : (d : ℝ) / b_r - 1 < (M : ℝ) := by
    have hmod_lt : d % bNat < bNat := Nat.mod_lt d hbNat_pos
    have hdiv_eq : bNat * M + d % bNat = d := Nat.div_add_mod d bNat
    have hd_lt : (d : ℝ) < b_r * ((M : ℝ) + 1) := by
      have hnat : d < bNat * (M + 1) := by nlinarith only [hmod_lt, hdiv_eq]
      have hreal : (d : ℝ) < ((bNat * (M + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
      rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, hbNat_cast] at hreal
      exact hreal
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hbr_pos]
    linarith
  have hexp_final : ((d - M * r : ℕ) : ℝ) + (r : ℝ) / (4 * b_r) * (d : ℝ) ≤
      1 + (1 - (r : ℝ) / (2 * b_r)) * (d : ℝ) := by
    rw [hsub_cast]
    have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
    have hMr_gt : ((d : ℝ) / b_r - 1) * (r : ℝ) < (M : ℝ) * (r : ℝ) :=
      mul_lt_mul_of_pos_right hM_gt hr_pos
    have h7r : 7 * (r : ℝ) < (r : ℝ) / (4 * b_r) * (d : ℝ) := by
      rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
      nlinarith only [mul_lt_mul_of_pos_left hd_gt_28b hr_pos]
    have ht1 : ((d : ℝ) / b_r - 1) * (r : ℝ) =
        4 * ((r : ℝ) / (4 * b_r) * (d : ℝ)) - (r : ℝ) := by
      field_simp
    have ht2 : (1 - (r : ℝ) / (2 * b_r)) * (d : ℝ) =
        (d : ℝ) - 2 * ((r : ℝ) / (4 * b_r) * (d : ℝ)) := by
      field_simp
      ring
    linarith
  have hball_nat := card_hamming_ball_pairs_le C_r k
  have hball_real : (pairs_C.card : ℝ) ≤
      (C_r.card : ℝ) * (∑ j ∈ Finset.Icc 1 k, (d.choose j : ℝ)) := by
    exact_mod_cast hball_nat
  calc
    (pairs_C.card : ℝ)
        ≤ (C_r.card : ℝ) * (∑ j ∈ Finset.Icc 1 k, (d.choose j : ℝ)) := hball_real
    _ ≤ (2 : ℝ) ^ ((d - M * r : ℕ) : ℝ) * (2 : ℝ) ^ ((r : ℝ) / (4 * b_r) * (d : ℝ)) := by
          rw [hcard_Cr]
          exact mul_le_mul_of_nonneg_left hsum_choose (by positivity)
    _ = (2 : ℝ) ^ (((d - M * r : ℕ) : ℝ) + (r : ℝ) / (4 * b_r) * (d : ℝ)) :=
          (Real.rpow_add (by norm_num) _ _).symm
    _ ≤ (2 : ℝ) ^ (1 + (1 - (r : ℝ) / (2 * b_r)) * (d : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_final
    _ = 2 * (2 : ℝ) ^ ((1 - (r : ℝ) / (2 * b_r)) * (d : ℝ)) := by
          rw [Real.rpow_add (by norm_num), Real.rpow_one]
    _ ≤ 2 * (P.card : ℝ) := mul_le_mul_of_nonneg_left hP_rate (by norm_num)
end HighDimSteinerSpanners.Proofs.Hamming
end
end

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.Hamming
namespace HighDimSteinerSpanners.Proofs.Hamming
theorem _root_.solution :
    ∀ (r d : ℕ), 4 ≤ r → 1 ≤ d →
      ∀ (p : ℝ), 1 ≤ p →
        let b_r : ℝ := (2 : ℝ) ^ r - 1
        let ρ_r : ℝ := 1 / (64 * b_r)
        ∀ (P : Finset (Fin d → Bool)),
          2 ≤ P.card →
          (2 : ℝ) ^ ((1 - (r : ℝ) / (2 * b_r)) * (d : ℝ)) ≤ (P.card : ℝ) →
          ∃ (S_r : Finset (Fin d → Bool)),
            Disjoint P S_r ∧
            ∃ (H_r : SimpleGraph ↥(P ∪ S_r)),
              let w := cubeSubgraphWeight p (P ∪ S_r)
              Nat.card H_r.edgeSet ≤ 2 * P.card ∧
              (∀ (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P),
                ENNReal.ofReal (cubeLpDist p x y) ≤
                  graphDist H_r w ⟨x, Finset.mem_union_left S_r hx⟩
                    ⟨y, Finset.mem_union_left S_r hy⟩) ∧
              (∀ (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P),
                (1 : ℝ) / 3 * ρ_r * (d : ℝ) ≤ (hammingDist x y : ℝ) →
                (hammingDist x y : ℝ) ≤ (9 : ℝ) / 4 * ρ_r * (d : ℝ) →
                ∃ q : H_r.Walk ⟨x, Finset.mem_union_left S_r hx⟩
                    ⟨y, Finset.mem_union_left S_r hy⟩,
                  q.IsPath ∧ q.length ≤ 3 ∧ walkWeight w q ≤ 387 * cubeLpDist p x y) := by
  intro r d hr hd p hp b_r ρ_r P _hP2 hP_rate
  let bNat : ℕ := 2 ^ r - 1
  have hbNat_ge15 : 15 ≤ bNat := by
    dsimp [bNat]
    have h16 : 16 ≤ 2 ^ r := le_trans (by norm_num : 16 ≤ 2 ^ 4) (Nat.pow_le_pow_right (by
        norm_num) hr)
    omega
  have hbNat_cast : (bNat : ℝ) = b_r := by
    dsimp [bNat, b_r]
    have h1 : 1 ≤ 2 ^ r := by omega
    rw [Nat.cast_sub h1]
    push_cast
    rfl
  have hbr_ge15 : (15 : ℝ) ≤ b_r := by rw [← hbNat_cast]; exact_mod_cast hbNat_ge15
  have hbr_pos : 0 < b_r := by linarith
  have hρ_pos : 0 < ρ_r := by dsimp [ρ_r]; positivity
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  by_cases h_small : (9 : ℝ) / 4 * ρ_r * (d : ℝ) < 1
  · refine ⟨∅, Finset.disjoint_empty_right P, ⊥, ?_⟩
    dsimp only
    refine ⟨?_, ?_, ?_⟩
    · have h0 : Nat.card (⊥ : SimpleGraph ↥(P ∪ ∅)).edgeSet ≤ (∅ : Finset (Sym2 ↥(P ∪ ∅))).card :=
        card_edgeSet_le_finset (⊥ : SimpleGraph ↥(P ∪ ∅)) ∅ (fun _ _ h => False.elim h)
      exact le_trans h0 (Nat.zero_le _)
    · intro x y hx hy
      exact cubeSubgraph_noncontracting hp P ∅ ⊥ x y hx hy
    · intro x y _ _ hlo hhi
      exfalso
      have hpos_real : (0 : ℝ) < (hammingDist x y : ℝ) := lt_of_lt_of_le (by positivity) hlo
      have hpos_nat : 1 ≤ hammingDist x y := by
        have : 0 < hammingDist x y := by exact_mod_cast hpos_real
        omega
      have hge1 : (1 : ℝ) ≤ (hammingDist x y : ℝ) := by exact_mod_cast hpos_nat
      linarith
  · push Not at h_small
    have hd_gt_28b : 28 * b_r < (d : ℝ) := by
      have h256 : 256 * b_r ≤ 9 * (d : ℝ) := by
        have h1 : 1 ≤ (9 : ℝ) / 4 * (1 / (64 * b_r)) * (d : ℝ) := h_small
        have hmul := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 256 * b_r by positivity)
        have heq : 256 * b_r * ((9 : ℝ) / 4 * (1 / (64 * b_r)) * (d : ℝ)) = 9 * (d : ℝ) := by
          field_simp; ring
        linarith
      linarith
    let C_r := blockCode r d
    let ψ_r := blockDecode r d
    let S_r := C_r \ P
    have h_union_eq : P ∪ S_r = P ∪ C_r := Finset.union_sdiff_self_eq_union
    have hP_sub : P ⊆ P ∪ S_r := Finset.subset_union_left
    have hC_sub : C_r ⊆ P ∪ S_r := h_union_eq ▸ Finset.subset_union_right
    let k : ℕ := ⌊(27 : ℝ) / 4 * ρ_r * (d : ℝ)⌋₊
    let H_r : SimpleGraph ↥(P ∪ S_r) :=
      { Adj := fun u v =>
          u ≠ v ∧
          ((u.val ∈ P ∧ v.val = ψ_r u.val) ∨
           (v.val ∈ P ∧ u.val = ψ_r v.val) ∨
           (u.val ∈ C_r ∧ v.val ∈ C_r ∧ hammingDist u.val v.val ≤ k))
        symm := ⟨fun u v h => by
          refine ⟨h.1.symm, ?_⟩
          rcases h.2 with h1 | h2 | ⟨huC, hvC, hdist⟩
          · exact Or.inr (Or.inl h1)
          · exact Or.inl h2
          · exact Or.inr (Or.inr ⟨hvC, huC, by rwa [hammingDist_comm]⟩)⟩
        loopless := ⟨fun u h => h.1 rfl⟩ }
    refine ⟨S_r, disjoint_sdiff_self_right, H_r, ?_⟩
    dsimp only
    set w := cubeSubgraphWeight p (P ∪ S_r)
    refine ⟨?_, ?_, ?_⟩
    · -- Edge count bound `Nat.card H_r.edgeSet ≤ 2 * P.card`
      let E₁ : Finset (Sym2 ↥(P ∪ S_r)) :=
        P.attach.image (fun x => s(⟨x.1, hP_sub x.2⟩, ⟨ψ_r x.1, hC_sub (blockDecode_mem r d x.1)⟩))
      let pairs_C := (C_r ×ˢ C_r).filter
        (fun cc' => 1 ≤ hammingDist cc'.1 cc'.2 ∧ hammingDist cc'.1 cc'.2 ≤ k)
      let toSym2 : ↥pairs_C → Sym2 ↥(P ∪ S_r) := fun p =>
        s(⟨p.1.1, hC_sub (Finset.mem_product.mp (Finset.mem_filter.mp p.2).1).1⟩,
          ⟨p.1.2, hC_sub (Finset.mem_product.mp (Finset.mem_filter.mp p.2).1).2⟩)
      let E₂ : Finset (Sym2 ↥(P ∪ S_r)) := Finset.univ.image toSym2
      have h_edges_sub : ∀ u v : ↥(P ∪ S_r), H_r.Adj u v → s(u, v) ∈ E₁ ∪ E₂ := by
        intro u v huv
        rcases huv with ⟨hne, hcase⟩
        have hval_ne : u.val ≠ v.val := fun heq => hne (Subtype.ext heq)
        rcases hcase with ⟨huP, hv_eq⟩ | ⟨hvP, hu_eq⟩ | ⟨huC, hvC, hdist⟩
        · apply Finset.mem_union_left
          rw [Finset.mem_image]
          refine ⟨⟨u.val, huP⟩, Finset.mem_attach _ _, ?_⟩
          have hv_sub : (⟨ψ_r u.val, hC_sub (blockDecode_mem r d u.val)⟩ : ↥(P ∪ S_r)) = v :=
            Subtype.ext hv_eq.symm
          rw [hv_sub]
        · apply Finset.mem_union_left
          rw [Sym2.eq_swap, Finset.mem_image]
          refine ⟨⟨v.val, hvP⟩, Finset.mem_attach _ _, ?_⟩
          have hu_sub : (⟨ψ_r v.val, hC_sub (blockDecode_mem r d v.val)⟩ : ↥(P ∪ S_r)) = u :=
            Subtype.ext hu_eq.symm
          rw [hu_sub]
        · apply Finset.mem_union_right
          rw [Finset.mem_image]
          have hpos : 1 ≤ hammingDist u.val v.val :=
            Nat.succ_le_of_lt (hammingDist_pos.mpr hval_ne)
          have hmem_p : (u.val, v.val) ∈ pairs_C := by
            rw [Finset.mem_filter, Finset.mem_product]
            exact ⟨⟨huC, hvC⟩, hpos, hdist⟩
          exact ⟨⟨(u.val, v.val), hmem_p⟩, Finset.mem_univ _, rfl⟩
      have hcard_H : Nat.card H_r.edgeSet ≤ E₁.card + E₂.card :=
        le_trans (card_edgeSet_le_finset H_r (E₁ ∪ E₂) h_edges_sub) (Finset.card_union_le E₁ E₂)
      have hE₁_card : E₁.card ≤ P.card := by
        calc
          E₁.card ≤ P.attach.card := Finset.card_image_le
          _ = P.card := Finset.card_attach
      have h2E₂ : 2 * E₂.card ≤ pairs_C.card :=
        two_mul_sym2_image_le (P ∪ S_r) C_r hC_sub k
      -- Binomial sum and codebook cardinality bound
      let α : ℝ := 7 * ρ_r
      have hα_pos : 0 < α := by dsimp [α]; positivity
      have hα_lt1 : α < 1 := by
        dsimp [α, ρ_r]
        rw [mul_one_div, div_lt_one (by positivity)]
        linarith
      have hk_le_αd : (k : ℝ) ≤ α * (d : ℝ) := by
        have hfl : (k : ℝ) ≤ (27 : ℝ) / 4 * ρ_r * (d : ℝ) := Nat.floor_le (by positivity)
        dsimp [α]
        linarith
      have hk_lt_d : k < d := by
        have hlt_real : (k : ℝ) < (d : ℝ) := by
          nlinarith only [hk_le_αd, mul_lt_mul_of_pos_right hα_lt1 hd_pos]
        exact_mod_cast hlt_real
      have hsum_choose :=
        @hamming_hsum_choose r d hr hbr_ge15 hα_pos hα_lt1
            hk_le_αd hk_lt_d
      have hpairs_real : (pairs_C.card : ℝ) ≤ 2 * (P.card : ℝ) :=
        blockCode_closePair_cardinality_bound r d k P (by omega) hbr_pos hd_gt_28b
          hP_rate hsum_choose
      have hpairs_nat : pairs_C.card ≤ 2 * P.card := by exact_mod_cast hpairs_real
      omega
    · -- Non-contraction
      intro x y hx hy
      exact cubeSubgraph_noncontracting hp P S_r H_r x y hx hy
    · -- 3-hop path with stretch ≤ 387
      intro x y hx hy hlo hhi
      have hxy_pos : (0 : ℝ) < (hammingDist x y : ℝ) := lt_of_lt_of_le (by positivity) hlo
      have hxy_ne : x ≠ y := by
        intro heq
        subst heq
        simp at hxy_pos
      let ux : ↥(P ∪ S_r) := ⟨x, Finset.mem_union_left S_r hx⟩
      let uy : ↥(P ∪ S_r) := ⟨y, Finset.mem_union_left S_r hy⟩
      let cx : ↥(P ∪ S_r) := ⟨ψ_r x, hC_sub (blockDecode_mem r d x)⟩
      let cy : ↥(P ∪ S_r) := ⟨ψ_r y, hC_sub (blockDecode_mem r d y)⟩
      have hux_ne_uy : ux ≠ uy := fun h => hxy_ne (Subtype.mk.inj h)
      have hadj_x : ux ≠ cx → H_r.Adj ux cx := fun hne => ⟨hne, Or.inl ⟨hx, rfl⟩⟩
      have hadj_y : cy ≠ uy → H_r.Adj cy uy := fun hne => ⟨hne, Or.inr (Or.inl ⟨hy, rfl⟩)⟩
      have hdist_c_le_3 : hammingDist (ψ_r x) (ψ_r y) ≤ 3 * hammingDist x y :=
        hammingDist_blockDecode_pair_le r d x y
      have hdist_c_le_k : hammingDist (ψ_r x) (ψ_r y) ≤ k := by
        have h3_le_k : 3 * hammingDist x y ≤ k := by
          apply Nat.le_floor
          push_cast
          linarith
        exact le_trans hdist_c_le_3 h3_le_k
      have hadj_c : cx ≠ cy → H_r.Adj cx cy := fun hne =>
        ⟨hne, Or.inr (Or.inr ⟨blockDecode_mem r d x, blockDecode_mem r d y, hdist_c_le_k⟩)⟩
      have hw_nn : ∀ a b : ↥(P ∪ S_r), 0 ≤ w s(a, b) := by
        intro a b
        dsimp [w]
        rw [cubeSubgraphWeight_mk]
        exact cubeLpDist_nonneg hp a.val b.val
      obtain ⟨q, hpath, hlen, hw_le⟩ :=
        exists_path_le_three H_r w hw_nn ux cx cy uy hux_ne_uy hadj_x hadj_c hadj_y
      have h_d_div_b : ((d / bNat : ℕ) : ℝ) ≤ 192 * (hammingDist x y : ℝ) := by
        calc
          ((d / bNat : ℕ) : ℝ)
              ≤ (d : ℝ) / (bNat : ℝ) := Nat.cast_div_le
          _ = 64 * ρ_r * (d : ℝ) := by
                rw [hbNat_cast]; dsimp [ρ_r]; field_simp
          _ ≤ 192 * (hammingDist x y : ℝ) := by linarith
      have hwx : cubeLpDist p x (ψ_r x) ≤ 192 * cubeLpDist p x y := by
        apply cubeLpDist_le_of_hamming_le hp (by norm_num)
        exact le_trans (by exact_mod_cast hammingDist_blockDecode_le r d x) h_d_div_b
      have hwy : cubeLpDist p (ψ_r y) y ≤ 192 * cubeLpDist p x y := by
        apply cubeLpDist_le_of_hamming_le hp (by norm_num)
        rw [hammingDist_comm]
        exact le_trans (by exact_mod_cast hammingDist_blockDecode_le r d y) h_d_div_b
      have hwc : cubeLpDist p (ψ_r x) (ψ_r y) ≤ 3 * cubeLpDist p x y := by
        apply cubeLpDist_le_of_hamming_le hp (by norm_num)
        exact_mod_cast hdist_c_le_3
      refine ⟨q, hpath, hlen, ?_⟩
      have hw_sum : w s(ux, cx) + w s(cx, cy) + w s(cy, uy) =
          cubeLpDist p x (ψ_r x) + cubeLpDist p (ψ_r x) (ψ_r y) + cubeLpDist p (ψ_r y) y := by
        simp only [w, cubeSubgraphWeight_mk, ux, uy, cx, cy]
      linarith
end HighDimSteinerSpanners.Proofs.Hamming

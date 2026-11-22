-- Prove2me | solution 1 for NOFSeparation750.CodedGIP.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-22T21:21:17.894516+00:00
-- url     : https://prove2.me/submissions/6f28f5b8-d878-40fe-856c-a7b9d6e29bb0

import Mathlib
import Definitions.Def_NOFSeparation750_CodedGIP_Model
import Theorems.Thm_NOFSeparation750_CodedGIP_fact_5_2
import Theorems.Thm_NOFSeparation750_CodedGIP_lemma_5_3
import Theorems.Thm_NOFSeparation750_CodedGIP_lemma_5_4

open NOFSeparation750.CodedGIP Finset

namespace T51Aux


theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

theorem decode_surjective {F : Type} [Field F] {r b : ℕ} (D : CodePair F r)
    (codec : (Fin b → Bool) ≃ F) (ℓ : ℕ) :
    Function.Surjective (decodeForehead D codec ℓ) := by
  classical
  intro y
  set m := D.small.dimension
  set mt := D.large.dimension
  let cA : Fin ℓ → Fin m → F := fun h i => D.small.basis.repr (y.1 h) i
  let cC : Fin mt → F := fun i => D.large.basis.repr y.2 i
  have hn : nativeLength D ℓ b = (ℓ * m + mt) * b := rfl
  have hb' : ∀ p : Fin (nativeLength D ℓ b), 0 < b := by
    intro p
    rcases Nat.eq_zero_or_pos b with h | h
    · have h1 := p.2.trans_eq hn
      have h2 : (ℓ * m + mt) * b = 0 := by rw [h, mul_zero]
      omega
    · exact h
  have hQ : ∀ p : Fin (nativeLength D ℓ b), p.val / b < ℓ * m + mt := by
    intro p
    rw [Nat.div_lt_iff_lt_mul (hb' p)]; exact p.2.trans_eq hn
  have hm' : ∀ p : Fin (nativeLength D ℓ b), p.val / b < ℓ * m → 0 < m := by
    intro p hQ'
    rcases Nat.eq_zero_or_pos m with h | h
    · have h2 : ℓ * m = 0 := by rw [h, mul_zero]
      exact absurd hQ' (by rw [h2]; exact Nat.not_lt_zero _)
    · exact h
  let x : Fin (nativeLength D ℓ b) → Bool := fun p =>
    if hQ' : p.val / b < ℓ * m then
      codec.symm (cA ⟨p.val / b / m, by rw [Nat.div_lt_iff_lt_mul (hm' p hQ')]; exact hQ'⟩
        ⟨p.val / b % m, Nat.mod_lt _ (hm' p hQ')⟩) ⟨p.val % b, Nat.mod_lt _ (hb' p)⟩
    else
      codec.symm (cC ⟨p.val / b - ℓ * m, by have := hQ p; omega⟩) ⟨p.val % b, Nat.mod_lt _ (hb' p)⟩
  refine ⟨x, ?_⟩
  have hA : ∀ (h : Fin ℓ) (i : Fin m),
      codec (fun t : Fin b => (List.ofFn x).getD ((h.val * m + i.val) * b + t.val) false) = cA h i := by
    intro h i
    rw [← codec.apply_symm_apply (cA h i)]
    congr 1
    funext t
    have hb : 0 < b := Nat.pos_of_ne_zero fun h0 => (h0 ▸ t).elim0
    have hidx : (h.val * m + i.val) * b + t.val < nativeLength D ℓ b := by
      rw [hn]
      have h1 : h.val * m + i.val < ℓ * m := by
        have := h.2; have := i.2; nlinarith
      have : (h.val * m + i.val) * b + t.val < (h.val * m + i.val + 1) * b := by nlinarith [t.2]
      calc _ < (h.val * m + i.val + 1) * b := this
        _ ≤ (ℓ * m + mt) * b := Nat.mul_le_mul_right _ (by omega)
    rw [getD_ofFn x _ hidx]
    have hdiv : ((h.val * m + i.val) * b + t.val) / b = h.val * m + i.val := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt t.2, zero_add]
    have hmod : ((h.val * m + i.val) * b + t.val) % b = t.val := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt t.2]
    have hm : 0 < m := Nat.pos_of_ne_zero fun h0 => (h0 ▸ i).elim0
    have hlt : h.val * m + i.val < ℓ * m := by
      have := h.2; have := i.2; nlinarith
    simp only [x, hdiv, hmod, dif_pos hlt]
    have e1 : (h.val * m + i.val) / m = h.val := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt i.2, zero_add]
    have e2 : (h.val * m + i.val) % m = i.val := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.2]
    simp only [e1, e2]
  have hC : ∀ (i : Fin mt),
      codec (fun t : Fin b => (List.ofFn x).getD ((ℓ * m + i.val) * b + t.val) false) = cC i := by
    intro i
    rw [← codec.apply_symm_apply (cC i)]
    congr 1
    funext t
    have hb : 0 < b := Nat.pos_of_ne_zero fun h0 => (h0 ▸ t).elim0
    have hidx : (ℓ * m + i.val) * b + t.val < nativeLength D ℓ b := by
      rw [hn]
      have : (ℓ * m + i.val) * b + t.val < (ℓ * m + i.val + 1) * b := by nlinarith [t.2]
      calc _ < (ℓ * m + i.val + 1) * b := this
        _ ≤ (ℓ * m + mt) * b := Nat.mul_le_mul_right _ (by omega)
    rw [getD_ofFn x _ hidx]
    have hdiv : ((ℓ * m + i.val) * b + t.val) / b = ℓ * m + i.val := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt t.2, zero_add]
    have hmod : ((ℓ * m + i.val) * b + t.val) % b = t.val := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt t.2]
    have hnlt : ¬ (ℓ * m + i.val < ℓ * m) := by omega
    simp only [x, hdiv, hmod, dif_neg hnlt, Nat.add_sub_cancel_left]
  unfold decodeForehead
  refine Prod.ext ?_ ?_
  · funext h
    simp only
    have : (fun a : Fin m => codec (fun t : Fin b =>
        (List.ofFn x).getD ((h.val * m + a.val) * b + t.val) false)) = cA h := funext (hA h)
    rw [this]
    simp only [CodePresentation.encode, cA]
    exact D.small.basis.sum_repr (y.1 h)
  · simp only
    have : (fun a : Fin mt => codec (fun t : Fin b =>
        (List.ofFn x).getD ((ℓ * m + a.val) * b + t.val) false)) = cC := funext hC
    rw [this]
    simp only [CodePresentation.encode, cC]
    exact D.large.basis.sum_repr y.2



theorem singleton_bound {F : Type} [Field F] {r : ℕ} (W : Submodule F (Fin r → F))
    (hd : 1 ≤ distance W) : Module.finrank F W + distance W ≤ r + 1 := by
  classical
  set d := distance W
  let T : Finset (Fin r) := univ.filter (fun t : Fin r => t.val < r + 1 - d)
  have hT : T.card = min r (r + 1 - d) := Fin.card_filter_val_lt
  let res : W →ₗ[F] (T → F) :=
    { toFun := fun a t => a.val t.val
      map_add' := fun a a' => by funext t; simp
      map_smul' := fun c a => by funext t; simp }
  have hinj : Function.Injective res := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    by_contra hne
    have hne' : a.val ≠ 0 := fun h => hne (Subtype.ext h)
    have hw : d ≤ weight a.val := Nat.sInf_le ⟨a.val, a.2, hne', rfl⟩
    have hsub : univ.filter (fun t => a.val t ≠ 0) ⊆ univ.filter (fun t => ¬ (t ∈ T)) := by
      intro t ht
      simp only [mem_filter, mem_univ, true_and] at ht ⊢
      intro htT
      exact ht (congrFun ha ⟨t, htT⟩)
    have hc := card_filter_add_card_filter_not (s := (univ : Finset (Fin r))) (fun t => t ∈ T)
    have hTT : (univ.filter fun t => t ∈ T) = T := by ext t; simp
    rw [hTT, card_univ, Fintype.card_fin, hT] at hc
    have := card_le_card hsub
    unfold weight at hw
    have hdr : d ≤ r + 1 := by
      by_contra h
      have : min r (r + 1 - d) = 0 := by omega
      omega
    omega
  have hdr : d ≤ r := by
    have hne : {d | ∃ x ∈ W, x ≠ 0 ∧ weight x = d}.Nonempty := Nat.nonempty_of_pos_sInf hd
    obtain ⟨x, -, -, hx⟩ := Nat.sInf_mem hne
    change weight x = d at hx
    rw [← hx]; unfold weight
    exact (card_filter_le _ _).trans (by simp)
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, hT] at this
  omega



section count
variable {F : Type} [Field F] [Fintype F] {r : ℕ} (D : CodePair F r) (ℓ k : ℕ)

def prodSum (y : Fin k → Forehead D ℓ) : Fin r → F :=
  ∑ h : Fin ℓ, (fun t => ∏ i : Fin k, ((y i).1 h).val t)

omit [Fintype F] in
theorem prodSum_mem (hprod : productCode D.small.code k ≤ D.large.code)
    (y : Fin k → Forehead D ℓ) : prodSum D ℓ k y ∈ D.large.code :=
  Submodule.sum_mem _ fun h _ => hprod (Submodule.subset_span ⟨fun i => (y i).1 h, rfl⟩)

def defect (hprod : productCode D.small.code k ≤ D.large.code) (y : Fin k → Forehead D ℓ) :
    D.large.code :=
  ⟨prodSum D ℓ k y - ∑ i, (y i).2.val,
    Submodule.sub_mem _ (prodSum_mem D ℓ k hprod y) (Submodule.sum_mem _ fun i _ => (y i).2.2)⟩

def shift (i0 : Fin k) (y : Fin k → Forehead D ℓ) (w : D.large.code) : Fin k → Forehead D ℓ :=
  Function.update y i0 ((y i0).1, (y i0).2 + w)

omit [Fintype F] in
theorem prodSum_shift (i0 : Fin k) (y : Fin k → Forehead D ℓ) (w : D.large.code) :
    prodSum D ℓ k (shift D ℓ k i0 y w) = prodSum D ℓ k y := by
  classical
  unfold prodSum shift
  congr 1; funext h; funext t; congr 1; funext i
  by_cases hi : i = i0
  · subst hi; simp
  · simp [Function.update_of_ne hi]

omit [Fintype F] in
theorem sumc_shift (i0 : Fin k) (y : Fin k → Forehead D ℓ) (w : D.large.code) :
    ∑ i, (shift D ℓ k i0 y w i).2.val = ∑ i, (y i).2.val + w.val := by
  classical
  unfold shift
  rw [← Finset.add_sum_erase _ _ (mem_univ i0), ← Finset.add_sum_erase _ _ (mem_univ i0)]
  simp only [Function.update_self, Submodule.coe_add]
  have : ∑ x ∈ univ.erase i0, (Function.update y i0 ((y i0).1, (y i0).2 + w) x).2.val =
      ∑ x ∈ univ.erase i0, (y x).2.val := by
    refine sum_congr rfl fun i hi => ?_
    rw [Function.update_of_ne (ne_of_mem_erase hi)]
  rw [this]; abel

omit [Fintype F] in
theorem codedGIP_iff (y : Fin k → Forehead D ℓ) :
    codedGIP D ℓ k y = true ↔ prodSum D ℓ k y = ∑ i, (y i).2.val := by
  unfold codedGIP prodSum; simp

theorem card_ones (hprod : productCode D.small.code k ≤ D.large.code) (i0 : Fin k) :
    Nat.card (Fin k → Forehead D ℓ) =
      Nat.card {y : Fin k → Forehead D ℓ // codedGIP D ℓ k y = true} *
        Nat.card D.large.code := by
  classical
  rw [← Nat.card_prod]
  refine Nat.card_congr
    { toFun := fun y => (⟨shift D ℓ k i0 y (defect D ℓ k hprod y), ?_⟩, defect D ℓ k hprod y)
      invFun := fun p => shift D ℓ k i0 p.1.1 (-p.2)
      left_inv := fun y => ?_
      right_inv := fun p => ?_ }
  · rw [codedGIP_iff, prodSum_shift, sumc_shift]
    simp [defect]
  · simp only [shift, Function.update_idem, Function.update_self, add_neg_cancel_right]
    exact Function.update_eq_self _ _
  · obtain ⟨⟨o, ho⟩, w⟩ := p
    rw [codedGIP_iff] at ho
    have hD : defect D ℓ k hprod (shift D ℓ k i0 o (-w)) = w := by
      apply Subtype.ext
      simp only [defect, prodSum_shift, sumc_shift, ho]
      simp
    simp only [hD]
    refine Prod.ext (Subtype.ext ?_) rfl
    simp only [shift, Function.update_idem, Function.update_self, neg_add_cancel_right]
    exact Function.update_eq_self _ _

end count


theorem core {F : Type} [Field F] [Fintype F] {r b ℓ k a' : ℕ} (hk : 2 ≤ k) (hℓ : 1 ≤ ℓ)
    (D : CodePair F r) (codec : (Fin b → Bool) ≃ F) {ε δ : ℝ}
    (hcomp : Compatible D.small.code D.large.code k ε δ) (hw : 1 ≤ ℓ * D.small.dimension)
    (ha : 1 ≤ a') (hF : Fintype.card F = 2 ^ a')
    (P : NondetProtocol (fun _ : Fin k => Bits (nativeLength D ℓ b))) (d : ℕ)
    (hP : P.Correct (nativeFunction D codec ℓ k)) (hd : P.Bounded d) :
    1 ≤ (2:ℝ) ^ d * (Nat.card D.large.code : ℝ) *
      Real.rpow (1 - (1 - 1 / (Fintype.card F : ℝ)) ^ (k - 1))
        (((ℓ * D.small.dimension : ℕ) : ℝ) / (2 : ℝ) ^ (k - 1)) := by
  classical
  obtain ⟨-, hr, -, -, -, -, -, hprod, -, -⟩ := hcomp
  set q : ℝ := (Fintype.card F : ℝ) with hq
  have hq1 : 1 < q := by
    rw [hq, hF]; exact_mod_cast Nat.one_lt_two_pow (by omega)
  set β' : ℝ := Real.rpow (1 - (1 - 1 / q) ^ (k - 1))
    (((ℓ * D.small.dimension : ℕ) : ℝ) / (2 : ℝ) ^ (k - 1)) with hβ'
  have hbase0 : 0 ≤ 1 - (1 - 1 / q) ^ (k - 1) := by
    have h1 : 0 ≤ 1 - 1 / q := by
      rw [sub_nonneg, div_le_one (by linarith)]; linarith
    have h2 : 1 - 1 / q ≤ 1 := by
      have : 0 ≤ 1 / q := by positivity
      linarith
    linarith [pow_le_one₀ h1 h2 (n := k - 1)]
  have hβ0 : 0 ≤ β' := Real.rpow_nonneg hbase0 _
  obtain ⟨t, ht, A, hA, hcov⟩ := fact_5_2 k _ _ P d hP hd
  let σ := Function.surjInv (decode_surjective D codec ℓ)
  have hσ : ∀ y, decodeForehead D codec ℓ (σ y) = y := Function.surjInv_eq _
  let A' : Fin t → Set (Fin k → Forehead D ℓ) := fun a => {y | (fun i => σ (y i)) ∈ A a}
  have hA'CI : ∀ a, IsCylinderIntersection (A' a) := by
    intro a
    obtain ⟨C, hC, hAC⟩ := (hA a).1
    refine ⟨fun i => {y | (fun i => σ (y i)) ∈ C i}, fun i => ?_, ?_⟩
    · intro y y' hyy
      exact hC i _ _ fun j hj => by simp only [hyy j hj]
    · ext y; simp [A', hAC]
  have hnat : ∀ y : Fin k → Forehead D ℓ,
      nativeFunction D codec ℓ k (fun i => σ (y i)) = codedGIP D ℓ k y := by
    intro y; simp only [nativeFunction, hσ]
  have hA'acc : ∀ a, A' a ⊆ {y | codedGIP D ℓ k y = true} := by
    intro a y hy
    have := (hA a).2 hy
    simp only [Set.mem_ofPred_eq, hnat] at this
    exact this
  have hcov' : ∀ y : Fin k → Forehead D ℓ, codedGIP D ℓ k y = true → ∃ a, y ∈ A' a := by
    intro y hy
    have : (fun i => σ (y i)) ∈ {x | nativeFunction D codec ℓ k x = true} := by
      simp only [Set.mem_ofPred_eq, hnat, hy]
    rw [hcov] at this
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp this
    exact ⟨a, ha⟩
  have hfib : ∀ a (c : Fin k → D.large.code),
      conditionalMass (A' a) {x | ∀ i, (x i).2 = c i} ≤ β' := by
    intro a c
    obtain ⟨B, τ, hB, hmass, hsub⟩ := lemma_5_4 k ℓ r hk hℓ hr F D (A' a) (hA'CI a) (hA'acc a) c
    have h53 := lemma_5_3 k (ℓ * D.small.dimension) a' hk hw ha F hF B hB τ
    have hBB : B ∩ {y | gip y = τ} = B := Set.inter_eq_left.mpr hsub
    rw [hBB] at h53
    rw [← hmass]
    have hu0 : 0 ≤ uniformMass B := by unfold uniformMass; positivity
    have : uniformMass B - uniformMass B / q = (1 - 1 / q) * uniformMass B := by ring
    rw [this, abs_of_nonneg (mul_nonneg (by rw [sub_nonneg, div_le_one (by linarith)]; linarith) hu0)] at h53
    have hpos : 0 < 1 - 1 / q := by
      rw [sub_pos, div_lt_one (by linarith)]; exact hq1
    exact le_of_mul_le_mul_left h53 hpos
  have hcardS : ∀ S : Set (Fin k → Forehead D ℓ),
      Nat.card {x // x ∈ S} = (univ.filter (· ∈ S)).card := by
    intro S; rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  let cmap : (Fin k → Forehead D ℓ) → (Fin k → D.large.code) := fun y i => (y i).2
  have hall : (Fintype.card (Fin k → Forehead D ℓ) : ℝ) =
      ∑ c, ((univ.filter (fun y => cmap y = c)).card : ℝ) := by
    rw [← card_univ, card_eq_sum_card_fiberwise (f := cmap) (t := univ) (fun _ _ => mem_univ _)]
    push_cast; rfl
  have hcountA : ∀ a, ((univ.filter (· ∈ A' a)).card : ℝ) ≤
      β' * (Fintype.card (Fin k → Forehead D ℓ) : ℝ) := by
    intro a
    rw [card_eq_sum_card_fiberwise (f := cmap) (t := univ) (fun _ _ => mem_univ _), hall, mul_sum]
    push_cast
    refine sum_le_sum fun c _ => ?_
    have h := hfib a c
    unfold conditionalMass at h
    have e1 : Nat.card {x // x ∈ A' a ∩ {x | ∀ i, (x i).2 = c i}} =
        ((univ.filter (· ∈ A' a)).filter (fun y => cmap y = c)).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      apply congrArg; ext y; simp [cmap, funext_iff]
    have e2 : Nat.card {x // x ∈ {x : Fin k → Forehead D ℓ | ∀ i, (x i).2 = c i}} =
        (univ.filter (fun y => cmap y = c)).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      apply congrArg; ext y; simp [cmap, funext_iff]
    rw [e1, e2] at h
    rcases Nat.eq_zero_or_pos (univ.filter fun y => cmap y = c).card with h0 | h0
    · have : ((univ.filter (· ∈ A' a)).filter (fun y => cmap y = c)).card = 0 := by
        apply Nat.eq_zero_of_le_zero; rw [← h0]; apply card_le_card
        intro y; simp only [mem_filter, mem_univ, true_and]; exact fun h => h.2
      rw [this, h0]; simp
    · rwa [div_le_iff₀ (by exact_mod_cast h0)] at h
  have hO : (univ.filter (fun y : Fin k → Forehead D ℓ => codedGIP D ℓ k y = true)).card ≤
      ∑ a, (univ.filter (· ∈ A' a)).card := by
    refine (card_le_card ?_).trans card_biUnion_le
    intro y hy
    simp only [mem_filter, mem_univ, true_and] at hy
    obtain ⟨a, ha⟩ := hcov' y hy
    exact mem_biUnion.mpr ⟨a, mem_univ _, by simpa using ha⟩
  have hones := card_ones D ℓ k hprod ⟨0, by omega⟩
  have hOc : Nat.card {y : Fin k → Forehead D ℓ // codedGIP D ℓ k y = true} =
      (univ.filter (fun y : Fin k → Forehead D ℓ => codedGIP D ℓ k y = true)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hOc, Nat.card_eq_fintype_card (α := Fin k → Forehead D ℓ)] at hones
  set cO := (univ.filter (fun y : Fin k → Forehead D ℓ => codedGIP D ℓ k y = true)).card
  set cX := Fintype.card (Fin k → Forehead D ℓ)
  set cW := Nat.card D.large.code
  have hcX : 0 < cX := Fintype.card_pos
  have hcO : 0 < cO := by
    rcases Nat.eq_zero_or_pos cO with h | h
    · rw [h, zero_mul] at hones; omega
    · exact h
  have h1 : (cO : ℝ) ≤ t * (β' * cX) := by
    calc (cO : ℝ) ≤ ∑ a, ((univ.filter (· ∈ A' a)).card : ℝ) := by exact_mod_cast hO
      _ ≤ ∑ _a : Fin t, β' * (cX : ℝ) := sum_le_sum fun a _ => hcountA a
      _ = t * (β' * cX) := by simp
  have h2 : (cX : ℝ) = cO * cW := by exact_mod_cast hones
  have ht' : (t : ℝ) ≤ 2 ^ d := by exact_mod_cast ht
  have hcO' : (0 : ℝ) < cO := by exact_mod_cast hcO
  rw [h2] at h1
  have h3 : (1 : ℝ) ≤ t * β' * cW := by
    have : (cO : ℝ) * 1 ≤ cO * (t * β' * cW) := by nlinarith
    exact le_of_mul_le_mul_left this hcO'
  calc (1 : ℝ) ≤ t * β' * cW := h3
    _ ≤ 2 ^ d * β' * cW := by gcongr
    _ = 2 ^ d * cW * β' := by ring

end T51Aux

open T51Aux in
theorem solution (k : ℕ) (hk : 2 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∃ j₀ : ℕ, ∀ a : ℕ, Allowed k a →
      ∀ (F : Type) [Field F] [Fintype F], ∀ D : PairFamily F a,
      ∀ codec : (Fin (2 * a) → Bool) ≃ F,
      (∀ j, Compatible (D j).small.code (D j).large.code k
        (6 / (2 ^ a : ℝ)) (3 / 4)) →
      ∀ j, j₀ ≤ j →
      ∀ P : NondetProtocol (fun _ : Fin k => Bits (nativeLength (D j) (copies k) (2 * a))),
      ∀ d : ℕ, P.Correct (nativeFunction (D j) codec (copies k) k) → P.Bounded d →
        c * (nativeLength (D j) (copies k) (2 * a) : ℝ) ≤ d := by
  refine ⟨1 / (2 ^ (k + 2) + 4), by positivity, 0, ?_⟩
  intro a ha F _ _ D codec hcomp j _ P d hP hd
  classical
  obtain ⟨ha1, hlo, hhi⟩ := ha
  set m := (D j).small.dimension with hm
  set mt := (D j).large.dimension with hmt
  set s := 2 ^ a with hs
  set L := 2 ^ (k + 2) with hL
  have hcj := hcomp j
  obtain ⟨-, hr1, -, -, -, -, hW0, -, hdimV, hdistW⟩ := hcj
  have hcardF : Fintype.card F = 2 ^ (2 * a) := by
    rw [← Fintype.card_congr codec]; simp
  have hq4 : (4 : ℕ) ^ a = s * s := by rw [hs, ← mul_pow]; norm_num
  -- basic facts
  have hfrV : Module.finrank F (D j).small.code = m := by
    rw [Module.finrank_eq_card_basis (D j).small.basis, Fintype.card_fin]
  have hfrW : Module.finrank F (D j).large.code = mt := by
    rw [Module.finrank_eq_card_basis (D j).large.basis, Fintype.card_fin]
  have hs2 : 2 ≤ s := by rw [hs]; exact Nat.le_self_pow (by omega) 2 |>.trans' (by norm_num)
  have hs64 : s ≤ 64 * k := by
    have : s ^ 2 ≤ (64 * k) ^ 2 := by rw [sq, ← hq4]; exact hhi
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp this
  have hs32 : 32 * k ≤ s := by
    have : (32 * k) ^ 2 ≤ s ^ 2 := by rw [sq s, ← hq4]; exact hlo
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp this
  have hrs : s ≤ (codeLength a j) := by
    rw [codeLength, ← hs, hq4]
    have h1 : s ≤ s * s - s := by
      have : 2 * s ≤ s * s := Nat.mul_le_mul_right s hs2
      omega
    exact h1.trans (Nat.le_mul_of_pos_right _ (pow_pos (by omega) _))
  have h6r : 6 * (codeLength a j) ≤ s * m := by
    rw [hfrV] at hdimV
    have hspos : (0:ℝ) < (s:ℝ) := by exact_mod_cast (show 0 < s by omega)
    have : (6 * (codeLength a j) : ℝ) ≤ s * m := by
      have h' := mul_le_mul_of_nonneg_left hdimV hspos.le
      rw [show ((2:ℝ) ^ a) = (s : ℝ) by rw [hs]; push_cast; ring] at h'
      rw [← mul_assoc, mul_div_cancel₀ _ hspos.ne'] at h'
      linarith
    exact_mod_cast this
  have hm6 : 6 ≤ m := by
    have : 6 * s ≤ s * m := (Nat.mul_le_mul_left 6 hrs).trans h6r
    rw [mul_comm] at this
    exact Nat.le_of_mul_le_mul_left this (by omega)
  have hdist : 3 * (codeLength a j) ≤ 4 * distance (D j).large.code := by
    have : (3 * (codeLength a j) : ℝ) ≤ 4 * distance (D j).large.code := by linarith
    exact_mod_cast this
  have hd1 : 1 ≤ distance (D j).large.code := by omega
  have hsing := singleton_bound (D j).large.code hd1
  rw [hfrW] at hsing
  have h4mt : 4 * mt ≤ (codeLength a j) + 4 := by omega
  -- core inequality
  have hw : 1 ≤ copies k * m := by
    unfold copies; have : 1 ≤ 2 ^ (k + 2) * k := Nat.one_le_iff_ne_zero.mpr (by positivity)
    nlinarith
  have hcore := core (a' := 2 * a) hk (by unfold copies; exact Nat.one_le_iff_ne_zero.mpr (by positivity)) (D j) codec (hcomp j) hw
    (by omega) hcardF P d hP hd
  -- simplify the core inequality
  set q : ℝ := (Fintype.card F : ℝ) with hq
  have hqs : q = (s : ℝ) * s := by
    rw [hq, hcardF, hs]; push_cast; ring
  have hcW : (Nat.card (D j).large.code : ℝ) = (s : ℝ) ^ (2 * mt) := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F), hfrW]
    push_cast; rw [← hq, hqs, pow_mul]; ring
  have hexp : (((copies k * m : ℕ) : ℝ) / (2 : ℝ) ^ (k - 1)) = ((8 * k * m : ℕ) : ℝ) := by
    unfold copies
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
    ring
  rw [hexp, Real.rpow_eq_pow, Real.rpow_natCast] at hcore
  set base : ℝ := 1 - (1 - 1 / q) ^ (k - 1) with hbase
  have hspos : (0:ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hq0 : (0:ℝ) < q := by rw [hqs]; positivity
  have hbase0 : 0 ≤ base := by
    have h1 : 0 ≤ 1 - 1 / q := by
      rw [sub_nonneg, div_le_one hq0, hqs]; nlinarith [show (2:ℝ) ≤ s by exact_mod_cast hs2]
    have h2 : 1 - 1 / q ≤ 1 := by have : 0 ≤ 1 / q := by positivity
                                  linarith
    linarith [pow_le_one₀ h1 h2 (n := k - 1)]
  have hbase_le : base ≤ 1 / s := by
    have hb := one_add_mul_le_pow (show (-2:ℝ) ≤ -(1/q) by
      have : 1 / q ≤ 1 := by rw [div_le_one hq0, hqs]; nlinarith [show (2:ℝ) ≤ s by exact_mod_cast hs2]
      linarith) (k - 1)
    have hk1 : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
    have h32 : (32 * k : ℝ) ≤ s := by exact_mod_cast hs32
    have : base ≤ ((k - 1 : ℕ) : ℝ) * (1 / q) := by
      rw [hbase]; rw [← sub_eq_add_neg] at hb; linarith
    calc base ≤ ((k - 1 : ℕ) : ℝ) * (1 / q) := this
      _ ≤ k * (1 / q) := by gcongr
      _ ≤ (s / 32) * (1 / q) := by gcongr; linarith
      _ = 1 / (32 * s) := by rw [hqs]; field_simp
      _ ≤ 1 / s := by gcongr; linarith
  have hpow : base ^ (8 * k * m) ≤ (1 / s) ^ (8 * k * m) := pow_le_pow_left₀ hbase0 hbase_le _
  rw [hcW] at hcore
  have h1 : (s : ℝ) ^ (8 * k * m) ≤ 2 ^ d * (s : ℝ) ^ (2 * mt) := by
    have := hcore.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
    rw [one_div_pow] at this
    have hpos : (0:ℝ) < (s : ℝ) ^ (8 * k * m) := by positivity
    rw [mul_one_div, le_div_iff₀ hpos, one_mul] at this
    exact this
  have h2 : 2 ^ (a * (8 * k * m)) ≤ 2 ^ (d + a * (2 * mt)) := by
    have : ((2 ^ (a * (8 * k * m)) : ℕ) : ℝ) ≤ ((2 ^ (d + a * (2 * mt)) : ℕ) : ℝ) := by
      have e : ((2:ℝ) ^ a) = (s : ℝ) := by rw [hs]; push_cast; ring
      have e1 : ((2 ^ (a * (8 * k * m)) : ℕ) : ℝ) = (s:ℝ) ^ (8 * k * m) := by
        push_cast; rw [pow_mul, e]
      have e2 : ((2 ^ (d + a * (2 * mt)) : ℕ) : ℝ) = 2 ^ d * (s:ℝ) ^ (2 * mt) := by
        push_cast; rw [pow_add, pow_mul, e]
      rw [e1, e2]; exact h1
    exact_mod_cast this
  have key : a * (8 * k * m) ≤ d + a * (2 * mt) :=
    (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
  -- linear arithmetic in X = a*k*m, Y = a*mt
  set X := a * (k * m) with hX
  set Y := a * mt with hY
  have k1 : 8 * X ≤ d + 2 * Y := by
    have e1 : a * (8 * k * m) = 8 * X := by rw [hX]; ring
    have e2 : a * (2 * mt) = 2 * Y := by rw [hY]; ring
    omega
  have k2 : 24 * Y ≤ 64 * X + 24 * a := by
    have h' : 24 * mt ≤ 64 * (k * m) + 24 := by
      have : 6 * (codeLength a j) ≤ 64 * k * m := h6r.trans (by
        calc s * m ≤ (64 * k) * m := Nat.mul_le_mul_right _ hs64
          _ = 64 * k * m := rfl)
      have : 64 * k * m = 64 * (k * m) := by ring
      omega
    have h'' := Nat.mul_le_mul_left a h'
    calc 24 * Y = a * (24 * mt) := by rw [hY]; ring
      _ ≤ a * (64 * (k * m) + 24) := h''
      _ = 64 * X + 24 * a := by rw [hX]; ring
  have k3 : 12 * a ≤ X := by
    have h12 : 2 * 6 ≤ k * m := Nat.mul_le_mul hk hm6
    calc 12 * a = a * 12 := by ring
      _ ≤ a * (k * m) := Nat.mul_le_mul_left a h12
      _ = X := rfl
  have hdX : 2 * X ≤ d := by omega
  have hY3 : Y ≤ 3 * X := by omega
  have hn : nativeLength (D j) (copies k) (2 * a) = 2 * L * X + 2 * Y := by
    unfold nativeLength copies; rw [hX, hY, hL]; ring
  rw [hn]
  have hL0 : (0:ℝ) < (L:ℝ) + 4 := by positivity
  have hLc : ((2:ℝ) ^ (k + 2) + 4) = (L:ℝ) + 4 := by rw [hL]; push_cast; ring
  rw [hLc, div_mul_eq_mul_div, one_mul, div_le_iff₀ hL0]
  have hdX' : (2 * X : ℝ) ≤ d := by exact_mod_cast hdX
  have hY3' : (Y : ℝ) ≤ 3 * X := by exact_mod_cast hY3
  push_cast
  have hX0 : (0:ℝ) ≤ X := by positivity
  calc (2 * (L:ℝ) * X + 2 * Y) ≤ (2 * (L:ℝ) * X + 2 * (3 * X)) := by linarith
    _ ≤ (2 * X) * ((L:ℝ) + 4) := by nlinarith
    _ ≤ d * ((L:ℝ) + 4) := mul_le_mul_of_nonneg_right hdX' hL0.le

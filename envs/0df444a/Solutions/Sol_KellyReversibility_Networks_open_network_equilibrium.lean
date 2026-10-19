-- Prove2me | solution 1 for KellyReversibility.Networks.open_network_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-17T06:54:26.853225+00:00
-- url     : https://prove2.me/submissions/2f6d3143-7238-440c-a20b-b3cf6b283776

-- Licensed under Apache 2.0. Full exact theorem: Kelly general-route open-network product-form equilibrium.
import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyReversibility_Networks_OpenNetwork
import Definitions.Def_KellyReversibility_Networks_ProductForm


open KellyReversibility.Networks
open scoped BigOperators

namespace KellyNetworkProof

variable {I J : ℕ} (N : Network I J)

noncomputable instance clsFintype (j : Fin J) : Fintype (N.Cls j) := by
  classical
  unfold Network.Cls
  infer_instance

noncomputable def wordWeight (j : Fin J) (c : List (N.Cls j)) : ℝ :=
  (c.map (fun x => N.ν x.1.1)).prod

theorem phiProd_zero (j : Fin J) : N.phiProd j 0 = 1 := by
  simp [Network.phiProd]

theorem phiProd_succ (j : Fin J) (n : ℕ) :
    N.phiProd j (n+1) = N.phiProd j n * N.φ j (n+1) := by
  exact Finset.prod_Icc_succ_top (by omega) _

theorem phiProd_pos (hN : N.IsValid) (j : Fin J) (n : ℕ) :
    0 < N.phiProd j n := by
  apply Finset.prod_pos
  intro l hl
  exact hN.φ_pos j l (by have := (Finset.mem_Icc.mp hl).1; omega)

theorem phiProd_fin (j : Fin J) (n : ℕ) :
    N.phiProd j n = ∏ l : Fin n, N.φ j (l+1) := by
  induction n with
  | zero => simp [phiProd_zero]
  | succ n ih => rw [phiProd_succ, Fin.prod_univ_castSucc, ih]; rfl

theorem queuePi_word (j : Fin J) (c : List (N.Cls j)) :
    N.queuePi j c = N.b j * wordWeight N j c / N.phiProd j c.length := by
  classical
  unfold Network.queuePi
  simp_rw [Network.alpha, (c.get _).property, if_true]
  rw [Finset.prod_div_distrib, phiProd_fin]
  have hw : (∏ l : Fin c.length, N.ν (c.get l).1.1) = wordWeight N j c := by
    unfold wordWeight
    conv_rhs => rw [← List.ofFn_get c, List.map_ofFn, List.prod_ofFn]
    rfl
  rw [hw]
  ring

theorem wordWeight_insert (j : Fin J) (c : List (N.Cls j)) (m : ℕ)
    (x : N.Cls j) (hm : m ≤ c.length) :
    wordWeight N j (c.insertIdx m x) = N.ν x.1.1 * wordWeight N j c := by
  unfold wordWeight
  rw [List.map_insertIdx]
  exact List.CommMonoid.prod_insertIdx (by simpa using hm)

theorem queuePi_insert_mul_phi (hN : N.IsValid) (j : Fin J)
    (c : List (N.Cls j)) (m : ℕ) (x : N.Cls j) (hm : m ≤ c.length) :
    N.queuePi j (c.insertIdx m x) * N.φ j (c.length+1) =
      N.queuePi j c * N.ν x.1.1 := by
  rw [queuePi_word, queuePi_word, wordWeight_insert N j c m x hm,
    List.length_insertIdx_of_le_length hm, phiProd_succ]
  have hp := ne_of_gt (phiProd_pos N hN j c.length)
  have hφ := ne_of_gt (hN.φ_pos j (c.length+1) (by omega))
  field_simp

end KellyNetworkProof


open KellyReversibility.Networks
open scoped BigOperators

namespace KellyNetworkProof

variable {I J : ℕ} (N : Network I J)

theorem sum_class_weights (j : Fin J) :
    (∑ x : N.Cls j, N.ν x.1.1) = N.a j := by
  classical
  unfold Network.a Network.alpha
  change (∑ x : {x : Σ i : Fin I, Fin (N.S i) // N.r x.1 x.2 = j}, N.ν x.1.1) = _
  have hh := Finset.sum_subtype (F := clsFintype N j) (p := fun x : Σ i : Fin I, Fin (N.S i) => N.r x.1 x.2 = j) (Finset.univ.filter (fun x : Σ i : Fin I, Fin (N.S i) => N.r x.1 x.2 = j)) (by simp) (fun x => N.ν x.1)
  calc
    _ = ∑ x ∈ Finset.univ.filter (fun x : Σ i : Fin I, Fin (N.S i) => N.r x.1 x.2 = j), N.ν x.1 := hh.symm
    _ = _ := by rw [Finset.sum_filter]; exact Fintype.sum_sigma _

theorem a_nonneg (hN : N.IsValid) (j : Fin J) : 0 ≤ N.a j := by
  rw [← sum_class_weights]
  exact Finset.sum_nonneg fun x _ => (hN.ν_pos x.1.1).le

theorem normalizer_pos (hN : N.IsValid) (j : Fin J)
    (hb : Summable (fun n : ℕ => N.a j ^ n / N.phiProd j n)) :
    0 < ∑' n : ℕ, N.a j ^ n / N.phiProd j n := by
  have h := hb.le_tsum 0 (fun n _ => div_nonneg
    (pow_nonneg (a_nonneg N hN j) n) (phiProd_pos N hN j n).le)
  simp only [pow_zero, phiProd_zero, div_one] at h
  linarith

theorem queuePi_pos (hN : N.IsValid) (j : Fin J)
    (hb : Summable (fun n : ℕ => N.a j ^ n / N.phiProd j n))
    (c : List (N.Cls j)) : 0 < N.queuePi j c := by
  unfold Network.queuePi
  apply mul_pos
  · exact inv_pos.mpr (normalizer_pos N hN j hb)
  · apply Finset.prod_pos
    intro l _
    apply div_pos
    · rw [Network.alpha, if_pos (c.get l).property]
      exact hN.ν_pos (c.get l).1.1
    · exact hN.φ_pos j (l+1) (by omega)

theorem queuePi_ofFn (j : Fin J) (n : ℕ) (v : Fin n → N.Cls j) :
    N.queuePi j (List.ofFn v) =
      N.b j * (∏ l, N.ν (v l).1.1) / N.phiProd j n := by
  rw [queuePi_word]
  simp [wordWeight, List.map_ofFn, List.prod_ofFn]

theorem sum_queuePi_ofFn (j : Fin J) (n : ℕ) :
    (∑ v : Fin n → N.Cls j, N.queuePi j (List.ofFn v)) =
      N.b j * (N.a j ^ n / N.phiProd j n) := by
  classical
  simp_rw [queuePi_ofFn]
  rw [← Finset.sum_div, ← Finset.mul_sum]
  have hh := Fintype.prod_sum (fun (_ : Fin n) (x : N.Cls j) => N.ν x.1.1)
  rw [← hh]
  simp only [sum_class_weights, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

theorem queuePi_hasSum (hN : N.IsValid) (j : Fin J)
    (hb : Summable (fun n : ℕ => N.a j ^ n / N.phiProd j n)) :
    HasSum (N.queuePi j) 1 := by
  classical
  let f : (Σ n : ℕ, Fin n → N.Cls j) → ℝ := fun p => N.queuePi j (List.ofFn p.2)
  have hf : Summable f := (summable_sigma_of_nonneg
    (fun p => (queuePi_pos N hN j hb _).le)).mpr ⟨fun _ => (hasSum_fintype _).summable, by
      simpa only [tsum_fintype, sum_queuePi_ofFn] using hb.mul_left (N.b j)⟩
  have ht : (∑' p, f p) = 1 := by
    rw [hf.tsum_sigma]
    simp only [f, tsum_fintype, sum_queuePi_ofFn]
    rw [tsum_mul_left]
    exact inv_mul_cancel₀ (ne_of_gt (normalizer_pos N hN j hb))
  have hs : HasSum f 1 := ht ▸ hf.hasSum
  exact (List.equivSigmaTuple.symm.hasSum_iff (f := N.queuePi j)).mp hs

end KellyNetworkProof


open scoped BigOperators

namespace KellyNetworkProof

set_option maxHeartbeats 1200000

theorem finite_product_hasSum {n : ℕ} (A : Fin n → Type*)
    (w : ∀ j, A j → ℝ) (hw : ∀ j x, 0 ≤ w j x)
    (hs : ∀ j, HasSum (w j) 1) :
    HasSum (fun x : ∀ j, A j => ∏ j, w j (x j)) 1 := by
  classical
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have ht := ih (fun j => A j.succ) (fun j => w j.succ)
      (fun j => hw j.succ) (fun j => hs j.succ)
    have hp := (hs 0).mul ht ((hs 0).summable.mul_of_nonneg ht.summable
      (hw 0) (fun x => Finset.prod_nonneg fun j _ => hw j.succ (x j)))
    apply (Fin.consEquiv A).hasSum_iff.mp
    simpa only [Function.comp_def, Fin.prod_univ_succ, Fin.consEquiv_apply,
      Fin.cons_zero, Fin.cons_succ, one_mul] using hp

end KellyNetworkProof


open KellyReversibility.Networks

namespace KellyNetworkProof

variable {I J : ℕ} (N : Network I J)

theorem netPi_pos (hN : N.IsValid)
    (hb : ∀ j, Summable (fun n : ℕ => N.a j ^ n / N.phiProd j n))
    (C : N.State) : 0 < N.netPi C := by
  exact Finset.prod_pos fun j _ => queuePi_pos N hN j (hb j) (C j)

theorem netPi_hasSum (hN : N.IsValid)
    (hb : ∀ j, Summable (fun n : ℕ => N.a j ^ n / N.phiProd j n)) :
    HasSum N.netPi 1 := by
  exact finite_product_hasSum (fun j => List (N.Cls j)) (N.queuePi)
    (fun j c => (queuePi_pos N hN j (hb j) c).le)
    (fun j => queuePi_hasSum N hN j (hb j))

end KellyNetworkProof


open KellyReversibility.Networks

namespace KellyNetworkProof

variable {I J : ℕ} (N : Network I J)

theorem insert_at (C : N.State) (j : Fin J) (m : ℕ) (x : N.Cls j) :
    N.insert C j m x j = (C j).insertIdx m x := by
  exact Function.update_self j ((C j).insertIdx m x) (fun k => C k)

theorem insert_away (C : N.State) {j k : Fin J} (h : k ≠ j)
    (m : ℕ) (x : N.Cls j) : N.insert C j m x k = C k := by
  exact Function.update_of_ne h ((C j).insertIdx m x) (fun k => C k)

theorem remove_at (C : N.State) (j : Fin J) (l : ℕ) :
    N.remove C j l j = (C j).eraseIdx l := by
  exact Function.update_self j ((C j).eraseIdx l) (fun k => C k)

theorem remove_away (C : N.State) {j k : Fin J} (h : k ≠ j) (l : ℕ) :
    N.remove C j l k = C k := by
  exact Function.update_of_ne h ((C j).eraseIdx l) (fun k => C k)

theorem remove_insert (C : N.State) (j : Fin J) (m : ℕ) (x : N.Cls j) :
    N.remove (N.insert C j m x) j m = C := by
  funext k
  by_cases h : k = j
  · subst k; rw [remove_at, insert_at, List.eraseIdx_insertIdx_self]
  · rw [remove_away N _ h, insert_away N _ h]

theorem insert_remove (C : N.State) (j : Fin J) (l : Fin (C j).length) :
    N.insert (N.remove C j l) j l ((C j).get l) = C := by
  funext k
  by_cases h : k = j
  · subst k
    rw [insert_at, remove_at]
    exact List.insertIdx_eraseIdx_getElem l.isLt
  · rw [insert_away N _ h, remove_away N _ h]

theorem insert_length (C : N.State) (j : Fin J) (m : ℕ) (x : N.Cls j)
    (hm : m ≤ (C j).length) :
    (N.insert C j m x j).length = (C j).length + 1 := by
  rw [insert_at, List.length_insertIdx_of_le_length hm]

theorem insert_get (C : N.State) (j : Fin J) (m : ℕ) (x : N.Cls j)
    (hm : m ≤ (C j).length) :
    (N.insert C j m x j).get ⟨m, by rw [insert_length N C j m x hm]; omega⟩ = x := by
  have aux : ∀ (L : List (N.Cls j)), L = (C j).insertIdx m x →
      ∀ hb : m < L.length, L.get ⟨m, hb⟩ = x := by
    intro L he hb
    subst L
    exact List.get_insertIdx_self (C j) x m hm
  exact aux _ (insert_at N C j m x) _

theorem insert_injective (j : Fin J) (m : ℕ) (x : N.Cls j) :
    Function.Injective (fun C : N.State => N.insert C j m x) := by
  intro C D h
  have := congrArg (fun E => N.remove E j m) h
  simpa only [remove_insert] using this

theorem remove_insert_comm (C : N.State) {j k : Fin J} (h : j ≠ k)
    (l m : ℕ) (x : N.Cls k) :
    N.remove (N.insert C k m x) j l = N.insert (N.remove C j l) k m x := by
  funext q
  by_cases hqj : q = j
  · subst q; rw [remove_at, insert_away N _ h, insert_away N _ h, remove_at]
  · by_cases hqk : q = k
    · subst q; rw [remove_away N _ (Ne.symm h), insert_at, insert_at, remove_away N _ (Ne.symm h)]
    · rw [remove_away N _ hqj, insert_away N _ hqk, insert_away N _ hqk, remove_away N _ hqj]

end KellyNetworkProof


open KellyReversibility.Networks
open scoped BigOperators

namespace KellyNetworkProof

variable {I J : ℕ} (N : Network I J)

theorem netPi_split (C : N.State) (j : Fin J) :
    N.netPi C = N.queuePi j (C j) *
      ∏ k ∈ Finset.univ.erase j, N.queuePi k (C k) := by
  classical
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm

theorem netPi_insert_mul_phi (hN : N.IsValid) (C : N.State) (j : Fin J)
    (m : ℕ) (x : N.Cls j) (hm : m ≤ (C j).length) :
    N.netPi (N.insert C j m x) * N.φ j ((C j).length+1) =
      N.netPi C * N.ν x.1.1 := by
  classical
  rw [netPi_split N (N.insert C j m x) j, netPi_split N C j, insert_at]
  have he : (∏ k ∈ Finset.univ.erase j, N.queuePi k (N.insert C j m x k)) =
      ∏ k ∈ Finset.univ.erase j, N.queuePi k (C k) := by
    apply Finset.prod_congr rfl
    intro k hk
    rw [insert_away N C (Finset.ne_of_mem_erase hk)]
  rw [he]
  have h := queuePi_insert_mul_phi N hN j (C j) m x hm
  linear_combination (∏ k ∈ Finset.univ.erase j, N.queuePi k (C k)) * h

theorem netPi_remove_mul_nu (hN : N.IsValid) (C : N.State) (j : Fin J)
    (l : Fin (C j).length) :
    N.netPi (N.remove C j l) * N.ν ((C j).get l).1.1 =
      N.netPi C * N.φ j (C j).length := by
  have hlen : (N.remove C j l j).length + 1 = (C j).length := by
    rw [remove_at, List.length_eraseIdx_of_lt l.isLt]
    have := l.isLt
    omega
  have hm : (l : ℕ) ≤ (N.remove C j l j).length := by
    rw [remove_at, List.length_eraseIdx_of_lt l.isLt]
    have := l.isLt
    omega
  have h := netPi_insert_mul_phi N hN (N.remove C j l) j l ((C j).get l) hm
  rw [insert_remove, hlen] at h
  exact h.symm

end KellyNetworkProof


open KellyReversibility.Networks

namespace KellyNetworkProof

theorem sum_fin_shift (f : ℕ → ℝ) (n : ℕ) :
    (∑ l : Fin n, f (l+1)) = ∑ l ∈ Finset.Icc 1 n, f l := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc, Finset.sum_Icc_succ_top (by omega)]
    simpa using congrArg (fun x => x + f (n+1)) ih

variable {I J : ℕ} (N : Network I J)

theorem gamma_sum_fin (hN : N.IsValid) (j : Fin J) (n : ℕ) (hn : 0 < n) :
    (∑ l : Fin n, N.γ j (l+1) n) = 1 := by
  exact (sum_fin_shift (fun l => N.γ j l n) n).trans (hN.γ_sum j n hn)

theorem delta_sum_fin (hN : N.IsValid) (j : Fin J) (n : ℕ) (hn : 0 < n) :
    (∑ l : Fin n, N.δ j (l+1) n) = 1 := by
  exact (sum_fin_shift (fun l => N.δ j l n) n).trans (hN.δ_sum j n hn)


theorem weighted_delta_sum (hN : N.IsValid) (j : Fin J) (n : ℕ) (hn : 0 < n) (a : ℝ) :
    (∑ l : Fin n, a * N.δ j (l+1) n) = a := by
  rw [← Finset.mul_sum, delta_sum_fin N hN j n hn, mul_one]

theorem weighted_gamma_sum (hN : N.IsValid) (j : Fin J) (n : ℕ) (hn : 0 < n) (a : ℝ) :
    (∑ l : Fin n, a * N.γ j (l+1) n) = a := by
  rw [← Finset.mul_sum, gamma_sum_fin N hN j n hn, mul_one]

end KellyNetworkProof


open scoped BigOperators
open KellyReversibility.Networks

namespace KellyNetworkProof

variable {I J : ℕ}

noncomputable def Lambda (N : Network I J) (C : N.State) : ℝ :=
  (∑ i, N.ν i) + ∑ j, if (C j).length = 0 then 0 else N.φ j (C j).length

def firstQueue (N : Network I J) (hN : N.IsValid) (i : Fin I) : Fin J :=
  N.r i ⟨0, hN.S_pos i⟩

def serviceChoices (N : Network I J) (C : N.State)
    (j : Fin J) (l : Fin (C j).length) : ℕ :=
  if h : ((C j).get l).1.2.1 + 1 < N.S ((C j).get l).1.1 then
    (C (N.r ((C j).get l).1.1 ⟨((C j).get l).1.2.1 + 1, h⟩)).length + 1
  else 1

def ArrivalEvent (N : Network I J) (hN : N.IsValid) (C : N.State) :=
  Σ i : Fin I, Fin ((C (firstQueue N hN i)).length + 1)

def ServiceEvent (N : Network I J) (C : N.State) :=
  Σ j : Fin J, Σ l : Fin (C j).length, Fin (serviceChoices N C j l)

instance (N : Network I J) (hN : N.IsValid) (C : N.State) :
    Fintype (ArrivalEvent N hN C) := by unfold ArrivalEvent; infer_instance

instance (N : Network I J) (C : N.State) :
    Fintype (ServiceEvent N C) := by unfold ServiceEvent; infer_instance

def Event (N : Network I J) (hN : N.IsValid) (C : N.State) :=
  ArrivalEvent N hN C ⊕ ServiceEvent N C

instance (N : Network I J) (hN : N.IsValid) (C : N.State) :
    Fintype (Event N hN C) := by unfold Event ArrivalEvent ServiceEvent; infer_instance

noncomputable def eventTarget (N : Network I J) (hN : N.IsValid) (C : N.State) :
    Event N hN C → N.State
  | .inl ⟨i, m⟩ => N.insert C (firstQueue N hN i) m (N.stageCls i 0 (hN.S_pos i))
  | .inr ⟨j, l, m⟩ =>
    if h : ((C j).get l).1.2.1 + 1 < N.S ((C j).get l).1.1 then
      N.insert (N.remove C j l)
        (N.r ((C j).get l).1.1 ⟨((C j).get l).1.2.1 + 1, h⟩) m
        (N.stageCls ((C j).get l).1.1 (((C j).get l).1.2.1 + 1) h)
    else N.remove C j l

noncomputable def eventWeight (N : Network I J) (hN : N.IsValid) (C : N.State) :
    Event N hN C → ℝ
  | .inl ⟨i, m⟩ => N.ν i * N.δ (firstQueue N hN i) (m + 1)
      ((C (firstQueue N hN i)).length + 1)
  | .inr ⟨j, l, m⟩ =>
    if h : ((C j).get l).1.2.1 + 1 < N.S ((C j).get l).1.1 then
      N.φ j (C j).length * N.γ j (l + 1) (C j).length *
        N.δ (N.r ((C j).get l).1.1 ⟨((C j).get l).1.2.1 + 1, h⟩) (m + 1)
        ((C (N.r ((C j).get l).1.1 ⟨((C j).get l).1.2.1 + 1, h⟩)).length + 1)
    else N.φ j (C j).length * N.γ j (l + 1) (C j).length

set_option backward.isDefEq.respectTransparency false in
theorem rate_eq_sum_event (N : Network I J) (hN : N.IsValid) (C D : N.State) :
    N.rate C D = ∑ e : Event N hN C,
      if D = eventTarget N hN C e then eventWeight N hN C e else 0 := by
  classical
  change N.rate C D = ∑ e : ArrivalEvent N hN C ⊕ ServiceEvent N C, _
  rw [Fintype.sum_sum_type]
  simp only [ArrivalEvent, ServiceEvent, Fintype.sum_sigma, eventTarget, eventWeight]
  rw [add_comm]
  unfold Network.rate
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    let f : ℕ → ℝ := fun m =>
      if D = (if h : ((C j).get l).1.2.1 + 1 < N.S ((C j).get l).1.1 then
        N.insert (N.remove C j l)
          (N.r ((C j).get l).1.1 ⟨((C j).get l).1.2.1 + 1, h⟩) m
          (N.stageCls ((C j).get l).1.1 (((C j).get l).1.2.1 + 1) h)
        else N.remove C j l) then
        (if h : ((C j).get l).1.2.1 + 1 < N.S ((C j).get l).1.1 then
          N.φ j (C j).length * N.γ j (l + 1) (C j).length *
            N.δ (N.r ((C j).get l).1.1 ⟨((C j).get l).1.2.1 + 1, h⟩) (m + 1)
              ((C (N.r ((C j).get l).1.1 ⟨((C j).get l).1.2.1 + 1, h⟩)).length + 1)
        else N.φ j (C j).length * N.γ j (l + 1) (C j).length)
      else 0
    change _ = ∑ m : Fin (serviceChoices N C j l), f m
    calc
      _ = ∑ m ∈ Finset.range (serviceChoices N C j l), f m := by
        dsimp only
        by_cases h : ((C j).get l).1.2.1 + 1 < N.S ((C j).get l).1.1
        · simp only [f, serviceChoices, dif_pos h]
        · simp only [f, serviceChoices, dif_neg h, Finset.sum_range_one]
      _ = _ := (Fin.sum_univ_eq_sum_range f (serviceChoices N C j l)).symm
  · apply Finset.sum_congr rfl
    intro i _
    simp only [dif_pos (hN.S_pos i), firstQueue]
    let f : ℕ → ℝ := fun m =>
      if D = N.insert C (N.r i ⟨0, hN.S_pos i⟩) m (N.stageCls i 0 (hN.S_pos i)) then
        N.ν i * N.δ (N.r i ⟨0, hN.S_pos i⟩) (m+1)
          ((C (N.r i ⟨0, hN.S_pos i⟩)).length+1)
      else 0
    exact (Fin.sum_univ_eq_sum_range f ((C (N.r i ⟨0,hN.S_pos i⟩)).length+1)).symm

end KellyNetworkProof


open KellyReversibility.Networks
open scoped BigOperators

namespace KellyNetworkProof

variable {I J : ℕ} (N : Network I J) (hN : N.IsValid)

theorem sum_eventWeight (C : N.State) :
    (∑ e : Event N hN C, eventWeight N hN C e) = Lambda N C := by
  classical
  change (∑ e : ArrivalEvent N hN C ⊕ ServiceEvent N C, eventWeight N hN C e) = _
  simp only [eventWeight]
  rw [Fintype.sum_sum_type]
  change (∑ p : Σ i : Fin I, Fin ((C (firstQueue N hN i)).length+1),
    N.ν p.1 * N.δ (firstQueue N hN p.1) (p.2+1)
      ((C (firstQueue N hN p.1)).length+1)) +
    (∑ p : Σ j : Fin J, Σ l : Fin (C j).length, Fin (serviceChoices N C j l),
      eventWeight N hN C (.inr p)) = _
  rw [Fintype.sum_sigma, Fintype.sum_sigma]
  unfold Lambda
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    exact weighted_delta_sum N hN (firstQueue N hN i) _ (Nat.succ_pos _) (N.ν i)
  · apply Finset.sum_congr rfl
    intro j _
    rw [Fintype.sum_sigma]
    have he : ∀ l : Fin (C j).length,
        (∑ m : Fin (serviceChoices N C j l), eventWeight N hN C (.inr ⟨j,l,m⟩)) =
        N.φ j (C j).length * N.γ j (l+1) (C j).length := by
      intro l
      let f : ℕ → ℝ := fun m =>
        if h : ((C j).get l).1.2.1+1 < N.S ((C j).get l).1.1 then
          N.φ j (C j).length * N.γ j (l+1) (C j).length *
            N.δ (N.r ((C j).get l).1.1 ⟨((C j).get l).1.2.1+1,h⟩)
              (m+1) ((C (N.r ((C j).get l).1.1 ⟨((C j).get l).1.2.1+1,h⟩)).length+1)
        else N.φ j (C j).length * N.γ j (l+1) (C j).length
      calc
        _ = ∑ m ∈ Finset.range (serviceChoices N C j l), f m :=
          Fin.sum_univ_eq_sum_range f _
        _ = _ := by
          by_cases h : ((C j).get l).1.2.1+1 < N.S ((C j).get l).1.1
          · simp only [f, serviceChoices, dif_pos h]
            let k := N.r ((C j).get l).1.1 ⟨((C j).get l).1.2.1+1,h⟩
            have hd := weighted_delta_sum N hN k ((C k).length+1) (Nat.succ_pos _)
              (N.φ j (C j).length * N.γ j (l+1) (C j).length)
            exact (Fin.sum_univ_eq_sum_range (fun m =>
              N.φ j (C j).length * N.γ j (l+1) (C j).length *
                N.δ k (m+1) ((C k).length+1)) ((C k).length+1)).symm.trans hd
          · simp only [f, serviceChoices, dif_neg h, Finset.sum_range_one]

    simp_rw [he]
    by_cases hn : (C j).length = 0
    · have : IsEmpty (Fin (C j).length) := ⟨fun l => by have := l.isLt; omega⟩
      simp only [Finset.univ_eq_empty, Finset.sum_empty, if_pos hn]
    · rw [if_neg hn]
      exact weighted_gamma_sum N hN j _ (by omega) _

include hN in
theorem outgoing_hasSum (C : N.State) :
    HasSum (N.rate C) (Lambda N C) := by
  classical
  have h := hasSum_sum (s := Finset.univ) (fun e _ =>
    hasSum_ite_eq (eventTarget N hN C e) (eventWeight N hN C e))
  rw [sum_eventWeight] at h
  exact h.congr_fun (fun D => rate_eq_sum_event N hN C D)

end KellyNetworkProof


open scoped BigOperators

namespace KellyNetworkProof

open scoped Classical in
theorem hasSum_finite_incidence {S : Type*} {E : S → Type*}
    [∀ s, Fintype (E s)] {T : Type*} [Fintype T]
    (target : (Σ s, E s) → S) (weight : (Σ s, E s) → ℝ) (C : S)
    (e : T ≃ {p : Σ s, E s // target p = C}) :
    HasSum (fun s => ∑ t : E s, if target ⟨s, t⟩ = C then weight ⟨s, t⟩ else 0)
      (∑ t : T, weight (e t).1) := by
  classical
  have hf : HasSum (fun p : {p : Σ s, E s // target p = C} => weight p.1)
      (∑ t : T, weight (e t).1) :=
    e.hasSum_iff.mp (hasSum_fintype (fun t : T => weight (e t).1))
  have hg : HasSum (fun p : Σ s, E s => if target p = C then weight p else 0)
      (∑ t : T, weight (e t).1) := by
    convert (hasSum_subtype_iff_indicator.mp hf) using 1
    funext p
    rfl
  exact hg.sigma (fun s => hasSum_fintype _)

end KellyNetworkProof


open KellyReversibility.Networks

namespace KellyNetworkProof

variable {I J : ℕ}

def firstClass (N : Network I J) (hN : N.IsValid) (i : Fin I) :
    N.Cls (firstQueue N hN i) := N.stageCls i 0 (hN.S_pos i)

def lastStage (N : Network I J) (hN : N.IsValid) (i : Fin I) : Fin (N.S i) :=
  ⟨N.S i - 1, by have := hN.S_pos i; omega⟩

def lastQueue (N : Network I J) (hN : N.IsValid) (i : Fin I) : Fin J :=
  N.r i (lastStage N hN i)

def lastClass (N : Network I J) (hN : N.IsValid) (i : Fin I) :
    N.Cls (lastQueue N hN i) := N.stageCls i (N.S i - 1) (lastStage N hN i).isLt

def RouteStep (N : Network I J) := Σ i : Fin I, {s : Fin (N.S i) // s.1 + 1 < N.S i}

def stepSource (N : Network I J) (t : RouteStep N) : Fin J := N.r t.1 t.2.1

def stepDestination (N : Network I J) (t : RouteStep N) : Fin J :=
  N.r t.1 ⟨t.2.1.1 + 1, t.2.2⟩

def stepOld (N : Network I J) (t : RouteStep N) : N.Cls (stepSource N t) :=
  N.stageCls t.1 t.2.1.1 t.2.1.isLt

def stepNew (N : Network I J) (t : RouteStep N) : N.Cls (stepDestination N t) :=
  N.stageCls t.1 (t.2.1.1 + 1) t.2.2

theorem step_ne (N : Network I J) (hN : N.IsValid) (t : RouteStep N) :
    stepSource N t ≠ stepDestination N t :=
  hN.r_succ_ne t.1 t.2.1.1 t.2.2

def IncomingArrival (N : Network I J) (hN : N.IsValid) (C : N.State) :=
  Σ i : Fin I, {l : Fin (C (firstQueue N hN i)).length //
    (C (firstQueue N hN i)).get l = firstClass N hN i}

def IncomingTransfer (N : Network I J) (C : N.State) :=
  Σ t : RouteStep N, Fin ((C (stepSource N t)).length + 1) ×
    {l : Fin (C (stepDestination N t)).length //
      (C (stepDestination N t)).get l = stepNew N t}

def IncomingDeparture (N : Network I J) (hN : N.IsValid) (C : N.State) :=
  Σ i : Fin I, Fin ((C (lastQueue N hN i)).length + 1)

noncomputable instance (N : Network I J) (hN : N.IsValid) (C : N.State) :
    Fintype (IncomingArrival N hN C) := by
  classical
  unfold IncomingArrival
  infer_instance

noncomputable instance (N : Network I J) (C : N.State) :
    Fintype (IncomingTransfer N C) := by
  classical
  unfold IncomingTransfer RouteStep
  infer_instance

instance (N : Network I J) (hN : N.IsValid) (C : N.State) :
    Fintype (IncomingDeparture N hN C) := by
  unfold IncomingDeparture
  infer_instance

def IncomingParam (N : Network I J) (hN : N.IsValid) (C : N.State) :=
  IncomingArrival N hN C ⊕ IncomingTransfer N C ⊕ IncomingDeparture N hN C

noncomputable instance (N : Network I J) (hN : N.IsValid) (C : N.State) :
    Fintype (IncomingParam N hN C) := by
  classical
  unfold IncomingParam IncomingArrival IncomingTransfer IncomingDeparture RouteStep
  infer_instance

def arrivalSource (N : Network I J) (hN : N.IsValid) (C : N.State)
    (p : IncomingArrival N hN C) : N.State := N.remove C (firstQueue N hN p.1) p.2.1

def transferSource (N : Network I J) (C : N.State)
    (p : IncomingTransfer N C) : N.State :=
  N.insert (N.remove C (stepDestination N p.1) p.2.2.1)
    (stepSource N p.1) p.2.1 (stepOld N p.1)

def departureSource (N : Network I J) (hN : N.IsValid) (C : N.State)
    (p : IncomingDeparture N hN C) : N.State :=
  N.insert C (lastQueue N hN p.1) p.2 (lastClass N hN p.1)

end KellyNetworkProof


open KellyReversibility.Networks

namespace KellyNetworkProof

variable {I J : ℕ}

def IncomingIncidence (N : Network I J) (hN : N.IsValid) (C : N.State) :=
  {p : Σ D : N.State, Event N hN D // eventTarget N hN p.1 p.2 = C}

theorem arrival_source_length (N : Network I J) (hN : N.IsValid) (C : N.State)
    (p : IncomingArrival N hN C) :
    (arrivalSource N hN C p (firstQueue N hN p.1)).length =
      (C (firstQueue N hN p.1)).length - 1 := by
  rw [arrivalSource, remove_at, List.length_eraseIdx_of_lt p.2.1.isLt]

def arrivalForward (N : Network I J) (hN : N.IsValid) (C : N.State)
    (p : IncomingArrival N hN C) : Event N hN (arrivalSource N hN C p) :=
  .inl ⟨p.1, ⟨p.2.1.1, by rw [arrival_source_length]; have := p.2.1.isLt; omega⟩⟩

theorem arrivalForward_target (N : Network I J) (hN : N.IsValid) (C : N.State)
    (p : IncomingArrival N hN C) :
    eventTarget N hN (arrivalSource N hN C p) (arrivalForward N hN C p) = C := by
  change N.insert (N.remove C (firstQueue N hN p.1) p.2.1)
    (firstQueue N hN p.1) p.2.1 (firstClass N hN p.1) = C
  exact (congrArg (fun x => N.insert (N.remove C (firstQueue N hN p.1) p.2.1)
    (firstQueue N hN p.1) p.2.1 x) p.2.2.symm).trans
      (insert_remove N C (firstQueue N hN p.1) p.2.1)

def arrivalIncidence (N : Network I J) (hN : N.IsValid) (C : N.State)
    (p : IncomingArrival N hN C) : IncomingIncidence N hN C :=
  ⟨⟨arrivalSource N hN C p, arrivalForward N hN C p⟩, arrivalForward_target N hN C p⟩

end KellyNetworkProof


open KellyReversibility.Networks

namespace KellyNetworkProof

variable {I J : ℕ}

theorem departure_source_length (N : Network I J) (hN : N.IsValid) (C : N.State)
    (p : IncomingDeparture N hN C) :
    (departureSource N hN C p (lastQueue N hN p.1)).length =
      (C (lastQueue N hN p.1)).length + 1 := by
  exact insert_length N C _ _ _ (by have := p.2.isLt; omega)

def departureIndex (N : Network I J) (hN : N.IsValid) (C : N.State)
    (p : IncomingDeparture N hN C) :
    Fin (departureSource N hN C p (lastQueue N hN p.1)).length :=
  ⟨p.2, by rw [departure_source_length]; exact p.2.isLt⟩

theorem departure_source_get (N : Network I J) (hN : N.IsValid) (C : N.State)
    (p : IncomingDeparture N hN C) :
    (departureSource N hN C p (lastQueue N hN p.1)).get (departureIndex N hN C p) =
      lastClass N hN p.1 := by
  exact insert_get N C _ _ _ (by have := p.2.isLt; omega)

set_option backward.isDefEq.respectTransparency false in
theorem departure_choices (N : Network I J) (hN : N.IsValid) (C : N.State)
    (p : IncomingDeparture N hN C) :
    serviceChoices N (departureSource N hN C p) (lastQueue N hN p.1)
      (departureIndex N hN C p) = 1 := by
  unfold serviceChoices
  rw [departure_source_get]
  simp only [lastClass, Network.stageCls]
  have hn : ¬ (N.S p.1 - 1 + 1 < N.S p.1) := by omega
  simp only [dif_neg hn]

def departureForward (N : Network I J) (hN : N.IsValid) (C : N.State)
    (p : IncomingDeparture N hN C) : Event N hN (departureSource N hN C p) :=
  .inr ⟨lastQueue N hN p.1, departureIndex N hN C p,
    ⟨0, by rw [departure_choices]; omega⟩⟩

set_option backward.isDefEq.respectTransparency false in
theorem departureForward_target (N : Network I J) (hN : N.IsValid) (C : N.State)
    (p : IncomingDeparture N hN C) :
    eventTarget N hN (departureSource N hN C p) (departureForward N hN C p) = C := by
  dsimp only [departureForward, eventTarget]
  rw [departure_source_get]
  simp only [lastClass, Network.stageCls]
  have hn : ¬ (N.S p.1 - 1 + 1 < N.S p.1) := by omega
  simp only [dif_neg hn]
  exact remove_insert N C _ _ _

def departureIncidence (N : Network I J) (hN : N.IsValid) (C : N.State)
    (p : IncomingDeparture N hN C) : IncomingIncidence N hN C :=
  ⟨⟨departureSource N hN C p, departureForward N hN C p⟩,
    departureForward_target N hN C p⟩

end KellyNetworkProof


open KellyReversibility.Networks

namespace KellyNetworkProof

variable {I J : ℕ}

theorem transfer_source_length (N : Network I J) (hN : N.IsValid) (C : N.State)
    (p : IncomingTransfer N C) :
    (transferSource N C p (stepSource N p.1)).length =
      (C (stepSource N p.1)).length + 1 := by
  unfold transferSource
  rw [insert_length, remove_away N _ (step_ne N hN p.1)]
  rw [remove_away N _ (step_ne N hN p.1)]
  have := p.2.1.isLt
  omega

def transferIndex (N : Network I J) (hN : N.IsValid) (C : N.State)
    (p : IncomingTransfer N C) :
    Fin (transferSource N C p (stepSource N p.1)).length :=
  ⟨p.2.1, by rw [transfer_source_length N hN]; exact p.2.1.isLt⟩

theorem transfer_source_get (N : Network I J) (hN : N.IsValid) (C : N.State)
    (p : IncomingTransfer N C) :
    (transferSource N C p (stepSource N p.1)).get (transferIndex N hN C p) =
      stepOld N p.1 := by
  apply insert_get N
  rw [remove_away N _ (step_ne N hN p.1)]
  have := p.2.1.isLt
  omega

theorem transfer_destination_length (N : Network I J) (hN : N.IsValid) (C : N.State)
    (p : IncomingTransfer N C) :
    (transferSource N C p (stepDestination N p.1)).length =
      (C (stepDestination N p.1)).length - 1 := by
  unfold transferSource
  rw [insert_away N _ (Ne.symm (step_ne N hN p.1)), remove_at,
    List.length_eraseIdx_of_lt p.2.2.1.isLt]

set_option backward.isDefEq.respectTransparency false in
theorem transfer_choices (N : Network I J) (hN : N.IsValid) (C : N.State)
    (p : IncomingTransfer N C) :
    serviceChoices N (transferSource N C p) (stepSource N p.1)
      (transferIndex N hN C p) = (C (stepDestination N p.1)).length := by
  unfold serviceChoices
  rw [transfer_source_get N hN]
  simp only [stepOld, Network.stageCls]
  simp only [dif_pos p.1.2.2]
  change (transferSource N C p (stepDestination N p.1)).length + 1 = _
  rw [transfer_destination_length N hN C p]
  have := p.2.2.1.isLt
  omega

def transferForward (N : Network I J) (hN : N.IsValid) (C : N.State)
    (p : IncomingTransfer N C) : Event N hN (transferSource N C p) :=
  .inr ⟨stepSource N p.1, transferIndex N hN C p,
    ⟨p.2.2.1, by rw [transfer_choices N hN]; exact p.2.2.1.isLt⟩⟩

set_option backward.isDefEq.respectTransparency false in
theorem transferForward_target (N : Network I J) (hN : N.IsValid) (C : N.State)
    (p : IncomingTransfer N C) :
    eventTarget N hN (transferSource N C p) (transferForward N hN C p) = C := by
  dsimp only [transferForward, eventTarget]
  rw [transfer_source_get N hN]
  simp only [stepOld, Network.stageCls]
  simp only [dif_pos p.1.2.2]
  change N.insert (N.remove (N.insert (N.remove C (stepDestination N p.1) p.2.2.1)
    (stepSource N p.1) p.2.1 (stepOld N p.1)) (stepSource N p.1) p.2.1)
    (stepDestination N p.1) p.2.2.1 (stepNew N p.1) = C
  rw [remove_insert]
  exact (congrArg (fun x => N.insert (N.remove C (stepDestination N p.1) p.2.2.1)
    (stepDestination N p.1) p.2.2.1 x) p.2.2.2.symm).trans
      (insert_remove N C (stepDestination N p.1) p.2.2.1)

def transferIncidence (N : Network I J) (hN : N.IsValid) (C : N.State)
    (p : IncomingTransfer N C) : IncomingIncidence N hN C :=
  ⟨⟨transferSource N C p, transferForward N hN C p⟩,
    transferForward_target N hN C p⟩

end KellyNetworkProof


open KellyReversibility.Networks

namespace KellyNetworkProof

variable {I J : ℕ}

def EventKey (N : Network I J) :=
  (Fin I × ℕ) ⊕ ((Σ i : Fin I, Fin (N.S i)) × Fin J × ℕ × ℕ)

def eventKey (N : Network I J) (hN : N.IsValid) (p : Σ D : N.State, Event N hN D) :
    EventKey N :=
  match p.2 with
  | .inl ⟨i, m⟩ => .inl (i, m)
  | .inr ⟨j, l, m⟩ => .inr (((p.1 j).get l).1, j, l, m)

theorem eventKey_injective (N : Network I J) (hN : N.IsValid) (C : N.State) :
    Function.Injective (fun e : Event N hN C => eventKey N hN ⟨C, e⟩) := by
  intro e f h
  rcases e with ⟨i, m⟩ | ⟨j, l, m⟩ <;>
    rcases f with ⟨i', m'⟩ | ⟨j', l', m'⟩
  · change Sum.inl (i, (m : ℕ)) = (Sum.inl (i', (m' : ℕ)) : EventKey N) at h
    have hi : i = i' := congrArg Prod.fst (Sum.inl.inj h)
    subst i'
    have hm : m = m' := Fin.ext (congrArg Prod.snd (Sum.inl.inj h))
    subst m'
    rfl
  · cases h
  · cases h
  · change Sum.inr (((C j).get l).1, j, (l : ℕ), (m : ℕ)) =
      (Sum.inr (((C j').get l').1, j', (l' : ℕ), (m' : ℕ)) : EventKey N) at h
    have ht := Sum.inr.inj h
    have hj : j = j' := congrArg (fun x => x.2.1) ht
    subst j'
    have hl : l = l' := Fin.ext (congrArg (fun x => x.2.2.1) ht)
    subst l'
    have hm : m = m' := Fin.ext (congrArg (fun x => x.2.2.2) ht)
    subst m'
    rfl

theorem event_pair_ext (N : Network I J) (hN : N.IsValid)
    (p q : Σ D : N.State, Event N hN D) (hs : p.1 = q.1)
    (hk : eventKey N hN p = eventKey N hN q) : p = q := by
  rcases p with ⟨C, e⟩
  rcases q with ⟨D, f⟩
  dsimp at hs
  subst D
  have he := eventKey_injective N hN C hk
  subst f
  rfl

end KellyNetworkProof


open KellyReversibility.Networks

namespace KellyNetworkProof

variable {I J : ℕ}

def incomingIncidence (N : Network I J) (hN : N.IsValid) (C : N.State) :
    IncomingParam N hN C → IncomingIncidence N hN C
  | .inl p => arrivalIncidence N hN C p
  | .inr (.inl p) => transferIncidence N hN C p
  | .inr (.inr p) => departureIncidence N hN C p

def incomingKey (N : Network I J) (hN : N.IsValid) (C : N.State) :
    IncomingParam N hN C → EventKey N
  | .inl p => .inl (p.1, p.2.1)
  | .inr (.inl p) => .inr (⟨p.1.1, p.1.2.1⟩, stepSource N p.1, p.2.1, p.2.2.1)
  | .inr (.inr p) => .inr (⟨p.1, lastStage N hN p.1⟩, lastQueue N hN p.1, p.2, 0)

theorem eventKey_incoming (N : Network I J) (hN : N.IsValid) (C : N.State)
    (p : IncomingParam N hN C) :
    eventKey N hN (incomingIncidence N hN C p).1 = incomingKey N hN C p := by
  rcases p with p | p | p
  · rfl
  · change Sum.inr (((transferSource N C p (stepSource N p.1)).get
        (transferIndex N hN C p)).1, stepSource N p.1, p.2.1.1, p.2.2.1.1) = _
    rw [transfer_source_get N hN]
    rfl
  · change Sum.inr (((departureSource N hN C p (lastQueue N hN p.1)).get
        (departureIndex N hN C p)).1, lastQueue N hN p.1, p.2.1, 0) = _
    rw [departure_source_get]
    rfl

theorem incomingKey_injective (N : Network I J) (hN : N.IsValid) (C : N.State) :
    Function.Injective (incomingKey N hN C) := by
  intro p q h
  rcases p with p | p | p <;> rcases q with q | q | q
  · rcases p with ⟨i, l, hl⟩
    rcases q with ⟨i', l', hl'⟩
    change Sum.inl (i, (l : ℕ)) = (Sum.inl (i', (l' : ℕ)) : EventKey N) at h
    have hi : i = i' := congrArg Prod.fst (Sum.inl.inj h)
    subst i'
    have : l = l' := Fin.ext (congrArg Prod.snd (Sum.inl.inj h))
    subst l'
    rfl
  · cases h
  · cases h
  · cases h
  · rcases p with ⟨⟨i, s, hs⟩, m, l, hl⟩
    rcases q with ⟨⟨i', s', hs'⟩, m', l', hl'⟩
    change Sum.inr (⟨i, s⟩, stepSource N ⟨i, s, hs⟩, (m : ℕ), (l : ℕ)) =
      (Sum.inr (⟨i', s'⟩, stepSource N ⟨i', s', hs'⟩, (m' : ℕ), (l' : ℕ)) : EventKey N) at h
    have h := Sum.inr.inj h
    simp only [Prod.mk.injEq] at h
    have hi : i = i' := congrArg Sigma.fst h.1
    subst i'
    have hss : s = s' := eq_of_heq (Sigma.mk.inj_iff.mp h.1).2
    subst s'
    have hmm : m = m' := Fin.ext h.2.2.1
    subst m'
    have hll : l = l' := Fin.ext h.2.2.2
    subst l'
    rfl
  · rcases p with ⟨⟨i, s, hs⟩, m, l, hl⟩
    rcases q with ⟨i', m'⟩
    change Sum.inr (⟨i, s⟩, stepSource N ⟨i, s, hs⟩, (m : ℕ), (l : ℕ)) =
      (Sum.inr (⟨i', lastStage N hN i'⟩, lastQueue N hN i', (m' : ℕ), 0) : EventKey N) at h
    have h := Sum.inr.inj h
    simp only [Prod.mk.injEq] at h
    have hi : i = i' := congrArg Sigma.fst h.1
    subst i'
    have hv := congrArg (fun z : Σ i : Fin I, Fin (N.S i) => z.2.1) h.1
    simp only [lastStage] at hv
    omega
  · cases h
  · rcases p with ⟨i, m⟩
    rcases q with ⟨⟨i', s, hs⟩, m', l, hl⟩
    change Sum.inr (⟨i, lastStage N hN i⟩, lastQueue N hN i, (m : ℕ), 0) =
      (Sum.inr (⟨i', s⟩, stepSource N ⟨i', s, hs⟩, (m' : ℕ), (l : ℕ)) : EventKey N) at h
    have h := Sum.inr.inj h
    simp only [Prod.mk.injEq] at h
    have hi : i = i' := congrArg Sigma.fst h.1
    subst i'
    have hv := congrArg (fun z : Σ i : Fin I, Fin (N.S i) => z.2.1) h.1
    simp only [lastStage] at hv
    omega
  · rcases p with ⟨i, m⟩
    rcases q with ⟨i', m'⟩
    change Sum.inr (⟨i, lastStage N hN i⟩, lastQueue N hN i, (m : ℕ), 0) =
      (Sum.inr (⟨i', lastStage N hN i'⟩, lastQueue N hN i', (m' : ℕ), 0) : EventKey N) at h
    have h := Sum.inr.inj h
    simp only [Prod.mk.injEq] at h
    have hi : i = i' := congrArg Sigma.fst h.1
    subst i'
    have hmm : m = m' := Fin.ext h.2.2.1
    subst m'
    rfl

theorem incomingIncidence_injective (N : Network I J) (hN : N.IsValid) (C : N.State) :
    Function.Injective (incomingIncidence N hN C) := by
  intro p q h
  apply incomingKey_injective N hN C
  simpa only [eventKey_incoming] using congrArg (fun r => eventKey N hN r.1) h

end KellyNetworkProof


open KellyReversibility.Networks

namespace KellyNetworkProof

variable {I J : ℕ}

theorem arrival_has_incoming (N : Network I J) (hN : N.IsValid) (D : N.State)
    (i : Fin I) (m : Fin ((D (firstQueue N hN i)).length + 1)) :
    ∃ p : IncomingParam N hN (eventTarget N hN D (.inl ⟨i, m⟩)),
      (incomingIncidence N hN _ p).1 = ⟨D, .inl ⟨i, m⟩⟩ := by
  let C := N.insert D (firstQueue N hN i) m (firstClass N hN i)
  have hm : m.1 ≤ (D (firstQueue N hN i)).length := by omega
  have hlen : (C (firstQueue N hN i)).length =
      (D (firstQueue N hN i)).length + 1 := insert_length N D _ _ _ hm
  let l : Fin (C (firstQueue N hN i)).length := ⟨m, by rw [hlen]; exact m.isLt⟩
  have hl : (C (firstQueue N hN i)).get l = firstClass N hN i :=
    insert_get N D _ _ _ hm
  let p : IncomingArrival N hN C := ⟨i, l, hl⟩
  refine ⟨.inl p, ?_⟩
  apply event_pair_ext N hN
  · exact remove_insert N D _ _ _
  · rfl

end KellyNetworkProof


open KellyReversibility.Networks

namespace KellyNetworkProof

variable {I J : ℕ}

set_option backward.isDefEq.respectTransparency false in
theorem transfer_has_incoming (N : Network I J) (hN : N.IsValid) (D : N.State)
    (t : RouteStep N) (l : Fin (D (stepSource N t)).length)
    (hl : (D (stepSource N t)).get l = stepOld N t)
    (m : Fin (serviceChoices N D (stepSource N t) l)) :
    ∃ p : IncomingParam N hN (eventTarget N hN D (.inr ⟨stepSource N t, l, m⟩)),
      (incomingIncidence N hN _ p).1 = ⟨D, .inr ⟨stepSource N t, l, m⟩⟩ := by
  have hchoices : serviceChoices N D (stepSource N t) l =
      (D (stepDestination N t)).length + 1 := by
    unfold serviceChoices
    rw [hl]
    simp only [stepOld, Network.stageCls, dif_pos t.2.2]
    rfl
  have hm : m.1 ≤ (D (stepDestination N t)).length := by
    have h := m.isLt
    omega
  let B := N.remove D (stepSource N t) l
  have hb : B (stepDestination N t) = D (stepDestination N t) :=
    remove_away N D (Ne.symm (step_ne N hN t)) l
  let C := N.insert B (stepDestination N t) m (stepNew N t)
  have htarget : eventTarget N hN D (.inr ⟨stepSource N t, l, m⟩) = C := by
    dsimp only [eventTarget]
    rw [hl]
    simp only [stepOld, Network.stageCls, dif_pos t.2.2]
    rfl
  have hc : (C (stepDestination N t)).length = (D (stepDestination N t)).length + 1 := by
    rw [insert_length N B _ _ _ (by rwa [hb]), hb]
  have hcs : (C (stepSource N t)).length = (D (stepSource N t)).length - 1 := by
    change (N.insert B (stepDestination N t) m (stepNew N t) (stepSource N t)).length = _
    rw [insert_away N B (step_ne N hN t) m (stepNew N t)]
    change (N.remove D (stepSource N t) l (stepSource N t)).length = _
    rw [remove_at N D (stepSource N t) l, List.length_eraseIdx_of_lt l.isLt]
  let ml : Fin (C (stepDestination N t)).length := ⟨m, by rw [hc]; omega⟩
  let lm : Fin ((C (stepSource N t)).length + 1) := ⟨l, by rw [hcs]; omega⟩
  have hget : (C (stepDestination N t)).get ml = stepNew N t :=
    insert_get N B _ _ _ (by rwa [hb])
  let p : IncomingTransfer N C := ⟨t, lm, ml, hget⟩
  have hs : transferSource N C p = D := by
    change N.insert (N.remove (N.insert B (stepDestination N t) m (stepNew N t))
      (stepDestination N t) m) (stepSource N t) l (stepOld N t) = D
    rw [remove_insert, ← hl]
    exact insert_remove N D _ l
  have hp : (incomingIncidence N hN C (.inr (.inl p))).1 =
      ⟨D, .inr ⟨stepSource N t, l, m⟩⟩ := by
    apply event_pair_ext N hN
    · exact hs
    · rw [eventKey_incoming]
      change Sum.inr (⟨t.1, t.2.1⟩, stepSource N t, l.1, m.1) =
        Sum.inr (((D (stepSource N t)).get l).1, stepSource N t, l.1, m.1)
      rw [hl]
      rfl
  rw [htarget]
  exact ⟨.inr (.inl p), hp⟩

end KellyNetworkProof


open KellyReversibility.Networks

namespace KellyNetworkProof

variable {I J : ℕ}

set_option backward.isDefEq.respectTransparency false in
theorem departure_has_incoming (N : Network I J) (hN : N.IsValid) (D : N.State)
    (i : Fin I) (l : Fin (D (lastQueue N hN i)).length)
    (hl : (D (lastQueue N hN i)).get l = lastClass N hN i)
    (m : Fin (serviceChoices N D (lastQueue N hN i) l)) :
    ∃ p : IncomingParam N hN (eventTarget N hN D (.inr ⟨lastQueue N hN i, l, m⟩)),
      (incomingIncidence N hN _ p).1 = ⟨D, .inr ⟨lastQueue N hN i, l, m⟩⟩ := by
  have hchoices : serviceChoices N D (lastQueue N hN i) l = 1 := by
    unfold serviceChoices
    rw [hl]
    simp only [lastClass, Network.stageCls]
    have hn : ¬ (N.S i - 1 + 1 < N.S i) := by omega
    simp only [dif_neg hn]
  have hm : m.1 = 0 := by
    have h := m.isLt
    omega
  let C := N.remove D (lastQueue N hN i) l
  have htarget : eventTarget N hN D (.inr ⟨lastQueue N hN i, l, m⟩) = C := by
    dsimp only [eventTarget]
    rw [hl]
    simp only [lastClass, Network.stageCls]
    have hn : ¬ (N.S i - 1 + 1 < N.S i) := by omega
    simp only [dif_neg hn]
    rfl
  have hlen : (C (lastQueue N hN i)).length = (D (lastQueue N hN i)).length - 1 := by
    change (N.remove D (lastQueue N hN i) l (lastQueue N hN i)).length = _
    rw [remove_at N D (lastQueue N hN i) l, List.length_eraseIdx_of_lt l.isLt]
  let lm : Fin ((C (lastQueue N hN i)).length + 1) := ⟨l, by rw [hlen]; omega⟩
  let p : IncomingDeparture N hN C := ⟨i, lm⟩
  have hs : departureSource N hN C p = D := by
    change N.insert (N.remove D (lastQueue N hN i) l) (lastQueue N hN i) l
      (lastClass N hN i) = D
    rw [← hl]
    exact insert_remove N D _ l
  have hp : (incomingIncidence N hN C (.inr (.inr p))).1 =
      ⟨D, .inr ⟨lastQueue N hN i, l, m⟩⟩ := by
    apply event_pair_ext N hN
    · exact hs
    · rw [eventKey_incoming]
      change Sum.inr (⟨i, lastStage N hN i⟩, lastQueue N hN i, l.1, 0) =
        Sum.inr (((D (lastQueue N hN i)).get l).1, lastQueue N hN i, l.1, m.1)
      rw [hl, hm]
      rfl
  rw [htarget]
  exact ⟨.inr (.inr p), hp⟩

end KellyNetworkProof


open KellyReversibility.Networks
open scoped BigOperators

namespace KellyNetworkProof

variable {I J : ℕ}

theorem event_has_incoming (N : Network I J) (hN : N.IsValid) (D : N.State)
    (e : Event N hN D) :
    ∃ p : IncomingParam N hN (eventTarget N hN D e),
      (incomingIncidence N hN _ p).1 = ⟨D, e⟩ := by
  rcases e with ⟨i, m⟩ | ⟨j, l, m⟩
  · exact arrival_has_incoming N hN D i m
  · generalize hx : (D j).get l = x at *
    rcases x with ⟨⟨i, s⟩, hroute⟩
    dsimp at hroute
    subst j
    have hl : (D (N.r i s)).get l = N.stageCls i s.1 s.isLt := hx
    by_cases hs : s.1 + 1 < N.S i
    · exact transfer_has_incoming N hN D ⟨i, s, hs⟩ l hl m
    · have he : s = lastStage N hN i := by
        apply Fin.ext
        have := s.isLt
        simp only [lastStage]
        omega
      subst s
      exact departure_has_incoming N hN D i l hl m

theorem incomingIncidence_surjective (N : Network I J) (hN : N.IsValid) (C : N.State) :
    Function.Surjective (incomingIncidence N hN C) := by
  rintro ⟨⟨D, e⟩, h⟩
  dsimp at h
  subst C
  obtain ⟨p, hp⟩ := event_has_incoming N hN D e
  exact ⟨p, Subtype.ext hp⟩

noncomputable def incomingEquiv (N : Network I J) (hN : N.IsValid) (C : N.State) :
    IncomingParam N hN C ≃ IncomingIncidence N hN C :=
  Equiv.ofBijective (incomingIncidence N hN C)
    ⟨incomingIncidence_injective N hN C, incomingIncidence_surjective N hN C⟩

noncomputable def incomingWeight (N : Network I J) (hN : N.IsValid) (C : N.State)
    (p : IncomingParam N hN C) : ℝ :=
  N.netPi (incomingIncidence N hN C p).1.1 *
    eventWeight N hN (incomingIncidence N hN C p).1.1 (incomingIncidence N hN C p).1.2

theorem hasSum_incoming_parameters (N : Network I J) (hN : N.IsValid) (C : N.State) :
    HasSum (fun D => N.netPi D * N.rate D C)
      (∑ p : IncomingParam N hN C, incomingWeight N hN C p) := by
  classical
  have h := hasSum_finite_incidence
    (fun p : Σ D : N.State, Event N hN D => eventTarget N hN p.1 p.2)
    (fun p => N.netPi p.1 * eventWeight N hN p.1 p.2) C (incomingEquiv N hN C)
  convert h using 1
  · funext D
    rw [rate_eq_sum_event N hN D C, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : C = eventTarget N hN D e
    · simp [he]
    · simp [he, Ne.symm he]
  · rfl

end KellyNetworkProof


open KellyReversibility.Networks

namespace KellyNetworkProof

variable {I J : ℕ} (N : Network I J) (hN : N.IsValid) (C : N.State)

theorem arrival_weight (p : IncomingArrival N hN C) :
    N.netPi (arrivalSource N hN C p) *
      eventWeight N hN (arrivalSource N hN C p) (arrivalForward N hN C p) =
    N.netPi C * N.φ (firstQueue N hN p.1) (C (firstQueue N hN p.1)).length *
      N.δ (firstQueue N hN p.1) (p.2.1+1) (C (firstQueue N hN p.1)).length := by
  have hh := netPi_remove_mul_nu N hN C (firstQueue N hN p.1) p.2.1
  have hν := congrArg (fun x : N.Cls (firstQueue N hN p.1) => N.ν x.1.1) p.2.2
  rw [hν] at hh
  change N.netPi (arrivalSource N hN C p) * N.ν p.1 = _ at hh
  have hl : (arrivalSource N hN C p (firstQueue N hN p.1)).length+1 =
      (C (firstQueue N hN p.1)).length := by
    rw [arrival_source_length]
    have := p.2.1.isLt
    omega
  change N.netPi (arrivalSource N hN C p) * (N.ν p.1 *
    N.δ (firstQueue N hN p.1) (p.2.1+1)
      ((arrivalSource N hN C p (firstQueue N hN p.1)).length+1)) = _
  rw [hl, ← mul_assoc, hh]

set_option backward.isDefEq.respectTransparency false in
theorem departure_weight (p : IncomingDeparture N hN C) :
    N.netPi (departureSource N hN C p) *
      eventWeight N hN (departureSource N hN C p) (departureForward N hN C p) =
    N.netPi C * N.ν p.1 * N.γ (lastQueue N hN p.1) (p.2+1)
      ((C (lastQueue N hN p.1)).length+1) := by
  have hh := netPi_insert_mul_phi N hN C (lastQueue N hN p.1) p.2
    (lastClass N hN p.1) (by have := p.2.isLt; omega)
  change N.netPi (departureSource N hN C p) *
    N.φ (lastQueue N hN p.1) ((C (lastQueue N hN p.1)).length+1) =
      N.netPi C * N.ν p.1 at hh
  unfold departureForward eventWeight
  dsimp only
  rw [departure_source_get]
  simp only [lastClass, Network.stageCls]
  rw [dif_neg (by have := hN.S_pos p.1; omega)]
  change N.netPi (departureSource N hN C p) *
    (N.φ (lastQueue N hN p.1) (departureSource N hN C p (lastQueue N hN p.1)).length *
      N.γ (lastQueue N hN p.1) (p.2+1) (departureSource N hN C p (lastQueue N hN p.1)).length) = _
  rw [departure_source_length, ← mul_assoc, hh]

include hN in
theorem transfer_mass (p : IncomingTransfer N C) :
    N.netPi (transferSource N C p) *
      N.φ (stepSource N p.1) ((C (stepSource N p.1)).length+1) =
    N.netPi C * N.φ (stepDestination N p.1) (C (stepDestination N p.1)).length := by
  have hrem := netPi_remove_mul_nu N hN C (stepDestination N p.1) p.2.2.1
  have hν := congrArg (fun x : N.Cls (stepDestination N p.1) => N.ν x.1.1) p.2.2.2
  rw [hν] at hrem
  have hins := netPi_insert_mul_phi N hN
    (N.remove C (stepDestination N p.1) p.2.2.1) (stepSource N p.1) p.2.1
    (stepOld N p.1) (by rw [remove_away N _ (step_ne N hN p.1)]; have := p.2.1.isLt; omega)
  rw [remove_away N _ (step_ne N hN p.1)] at hins
  exact hins.trans hrem

set_option backward.isDefEq.respectTransparency false in
theorem transfer_weight (p : IncomingTransfer N C) :
    N.netPi (transferSource N C p) *
      eventWeight N hN (transferSource N C p) (transferForward N hN C p) =
    N.netPi C * N.φ (stepDestination N p.1) (C (stepDestination N p.1)).length *
      N.δ (stepDestination N p.1) (p.2.2.1+1) (C (stepDestination N p.1)).length *
      N.γ (stepSource N p.1) (p.2.1+1) ((C (stepSource N p.1)).length+1) := by
  have hl : (transferSource N C p (stepDestination N p.1)).length+1 =
      (C (stepDestination N p.1)).length := by
    rw [transfer_destination_length N hN]
    have := p.2.2.1.isLt
    omega
  unfold transferForward eventWeight
  dsimp only
  rw [transfer_source_get N hN]
  simp only [stepOld, Network.stageCls, dif_pos p.1.2.2]
  change N.netPi (transferSource N C p) *
    (N.φ (stepSource N p.1) (transferSource N C p (stepSource N p.1)).length *
    N.γ (stepSource N p.1) (p.2.1+1) (transferSource N C p (stepSource N p.1)).length *
    N.δ (stepDestination N p.1) (p.2.2.1+1)
      ((transferSource N C p (stepDestination N p.1)).length+1)) = _
  rw [transfer_source_length N hN, hl]
  have hh := transfer_mass N hN C p
  linear_combination (N.γ (stepSource N p.1) (p.2.1+1) ((C (stepSource N p.1)).length+1) *
    N.δ (stepDestination N p.1) (p.2.2.1+1) (C (stepDestination N p.1)).length) * hh

end KellyNetworkProof


open KellyReversibility.Networks

namespace KellyNetworkProof

variable {I J : ℕ}

def SuccessorOccurrence (N : Network I J) (C : N.State) :=
  Σ t : RouteStep N, {l : Fin (C (stepDestination N t)).length //
    (C (stepDestination N t)).get l = stepNew N t}

def CurrentPosition (N : Network I J) (C : N.State) := Σ j : Fin J, Fin (C j).length

noncomputable instance (N : Network I J) (C : N.State) : Fintype (SuccessorOccurrence N C) := by
  classical
  unfold SuccessorOccurrence RouteStep
  infer_instance

instance (N : Network I J) (C : N.State) : Fintype (CurrentPosition N C) := by
  unfold CurrentPosition
  infer_instance

def occurrencePosition (N : Network I J) (hN : N.IsValid) (C : N.State) :
    IncomingArrival N hN C ⊕ SuccessorOccurrence N C → CurrentPosition N C
  | .inl p => ⟨firstQueue N hN p.1, p.2.1⟩
  | .inr p => ⟨stepDestination N p.1, p.2.1⟩

def positionClass (N : Network I J) (C : N.State) (p : CurrentPosition N C) :
    Σ i : Fin I, Fin (N.S i) := ((C p.1).get p.2).1

theorem positionClass_arrival (N : Network I J) (hN : N.IsValid) (C : N.State)
    (p : IncomingArrival N hN C) :
    positionClass N C (occurrencePosition N hN C (.inl p)) = ⟨p.1, ⟨0,hN.S_pos p.1⟩⟩ := by
  change ((C (firstQueue N hN p.1)).get p.2.1).1 = _
  rw [p.2.2]
  rfl

theorem positionClass_successor (N : Network I J) (hN : N.IsValid) (C : N.State)
    (p : SuccessorOccurrence N C) :
    positionClass N C (occurrencePosition N hN C (.inr p)) =
      ⟨p.1.1, ⟨p.1.2.1.1+1,p.1.2.2⟩⟩ := by
  change ((C (stepDestination N p.1)).get p.2.1).1 = _
  rw [p.2.2]
  rfl

theorem occurrencePosition_injective (N : Network I J) (hN : N.IsValid) (C : N.State) :
    Function.Injective (occurrencePosition N hN C) := by
  intro p q he
  have hc := congrArg (positionClass N C) he
  have hl := congrArg (fun z : CurrentPosition N C => z.2.1) he
  rcases p with p | p <;> rcases q with q | q
  · rw [positionClass_arrival, positionClass_arrival] at hc
    have hi := congrArg Sigma.fst hc
    rcases p with ⟨i,l,hlp⟩; rcases q with ⟨i',l',hlq⟩
    dsimp at hi
    subst i'
    have hll : l = l' := Fin.ext hl
    subst l'
    rfl
  · rw [positionClass_arrival, positionClass_successor] at hc
    have hv := congrArg (fun z : Σ i : Fin I, Fin (N.S i) => z.2.1) hc
    simp only at hv
    omega
  · rw [positionClass_successor, positionClass_arrival] at hc
    have hv := congrArg (fun z : Σ i : Fin I, Fin (N.S i) => z.2.1) hc
    simp only at hv
    omega
  · rw [positionClass_successor, positionClass_successor] at hc
    have hi := congrArg Sigma.fst hc
    have hv := congrArg (fun z : Σ i : Fin I, Fin (N.S i) => z.2.1) hc
    rcases p with ⟨⟨i,s,hs⟩,l,hlp⟩; rcases q with ⟨⟨i',s',hs'⟩,l',hlq⟩
    dsimp at hi hv
    subst i'
    have hss : s = s' := Fin.ext (by omega)
    subst s'
    have hll : l = l' := Fin.ext hl
    subst l'
    rfl

theorem occurrencePosition_surjective (N : Network I J) (hN : N.IsValid) (C : N.State) :
    Function.Surjective (occurrencePosition N hN C) := by
  rintro ⟨j,l⟩
  let x := (C j).get l
  rcases hx : x.1 with ⟨i,s⟩
  have hr : N.r i s = j :=
    (congrArg (fun z : Σ i : Fin I, Fin (N.S i) => N.r z.1 z.2) hx).symm.trans x.2
  by_cases hs : s.1 = 0
  · have hsz : s = ⟨0,hN.S_pos i⟩ := Fin.ext hs
    subst s
    have hj : firstQueue N hN i = j := hr
    cases hj
    refine ⟨.inl ⟨i,l,?_⟩,rfl⟩
    apply Subtype.ext
    exact hx
  · have hst := s.isLt
    let t : RouteStep N := ⟨i,⟨⟨s.1-1,by omega⟩,by change s.1-1+1<N.S i; omega⟩⟩
    have hss : (⟨t.2.1.1+1,t.2.2⟩ : Fin (N.S i)) = s := Fin.ext (by dsimp [t]; omega)
    have hj : stepDestination N t = j := by unfold stepDestination; rw [hss]; exact hr
    let l' : Fin (C (stepDestination N t)).length :=
      Fin.cast (congrArg (fun q => (C q).length) hj.symm) l
    have he : (⟨stepDestination N t,l'⟩ : CurrentPosition N C) = ⟨j,l⟩ := by
      apply Sigma.ext hj
      exact (Fin.heq_ext_iff (congrArg (fun q => (C q).length) hj)).mpr rfl
    refine ⟨.inr ⟨t,l',?_⟩,he⟩
    apply Subtype.ext
    change positionClass N C ⟨stepDestination N t,l'⟩ = ⟨i,⟨t.2.1.1+1,t.2.2⟩⟩
    rw [he, hss]
    exact hx

noncomputable def occurrenceEquiv (N : Network I J) (hN : N.IsValid) (C : N.State) :
    IncomingArrival N hN C ⊕ SuccessorOccurrence N C ≃ CurrentPosition N C :=
  Equiv.ofBijective _ ⟨occurrencePosition_injective N hN C,
    occurrencePosition_surjective N hN C⟩

end KellyNetworkProof


open KellyReversibility.Networks
open scoped BigOperators

namespace KellyNetworkProof

variable {I J : ℕ} (N : Network I J) (hN : N.IsValid) (C : N.State)

noncomputable def positionFlux (p : CurrentPosition N C) : ℝ :=
  N.netPi C * N.φ p.1 (C p.1).length * N.δ p.1 (p.2+1) (C p.1).length

set_option backward.isDefEq.respectTransparency false in
include hN in
theorem sum_positionFlux :
    (∑ p : CurrentPosition N C, positionFlux N C p) =
    N.netPi C * ∑ j, if (C j).length = 0 then 0 else N.φ j (C j).length := by
  classical
  change (∑ p : Σ j : Fin J, Fin (C j).length, _) = _
  rw [Fintype.sum_sigma, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold positionFlux
  by_cases hn : (C j).length = 0
  · have : IsEmpty (Fin (C j).length) := ⟨fun l => by have := l.isLt; omega⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty, if_pos hn, mul_zero]
  · rw [if_neg hn]
    exact weighted_delta_sum N hN j (C j).length (Nat.pos_of_ne_zero hn) (N.netPi C * N.φ j (C j).length)

set_option backward.isDefEq.respectTransparency false in
theorem sum_arrival_transfer :
    (∑ p : IncomingArrival N hN C,
      positionFlux N C (occurrencePosition N hN C (.inl p))) +
    (∑ p : SuccessorOccurrence N C,
      positionFlux N C (occurrencePosition N hN C (.inr p))) =
    N.netPi C * ∑ j, if (C j).length = 0 then 0 else N.φ j (C j).length := by
  classical
  have h := ((occurrenceEquiv N hN C).sum_comp (positionFlux N C)).trans
    (sum_positionFlux N hN C)
  exact (Fintype.sum_sum_type (fun p => positionFlux N C (occurrencePosition N hN C p))).symm.trans h

set_option backward.isDefEq.respectTransparency false in
theorem sum_incomingWeight :
    (∑ p : IncomingParam N hN C, incomingWeight N hN C p) =
      N.netPi C * Lambda N C := by
  classical
  unfold IncomingParam
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have ha : (∑ p : IncomingArrival N hN C, incomingWeight N hN C (.inl p)) =
      ∑ p : IncomingArrival N hN C,
        positionFlux N C (occurrencePosition N hN C (.inl p)) := by
    apply Finset.sum_congr rfl
    intro p _
    exact arrival_weight N hN C p
  have ht : (∑ p : IncomingTransfer N C, incomingWeight N hN C (.inr (.inl p))) =
      ∑ p : SuccessorOccurrence N C,
        positionFlux N C (occurrencePosition N hN C (.inr p)) := by
    simp only [IncomingTransfer, SuccessorOccurrence, Fintype.sum_sigma,
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    simp_rw [show ∀ m, incomingWeight N hN C (.inr (.inl ⟨t,m,l⟩)) =
      positionFlux N C ⟨stepDestination N t,l.1⟩ *
        N.γ (stepSource N t) (m+1) ((C (stepSource N t)).length+1) from
      fun m => transfer_weight N hN C ⟨t,m,l⟩]
    rw [← Finset.mul_sum, gamma_sum_fin N hN _ _ (by omega), mul_one]
    rfl
  have hd : (∑ p : IncomingDeparture N hN C, incomingWeight N hN C (.inr (.inr p))) =
      N.netPi C * ∑ i, N.ν i := by
    change (∑ p : Σ i : Fin I, Fin ((C (lastQueue N hN i)).length+1), _) = _
    rw [Fintype.sum_sigma, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp_rw [show ∀ m, incomingWeight N hN C (.inr (.inr ⟨i,m⟩)) =
      N.netPi C * N.ν i * N.γ (lastQueue N hN i) (m+1)
        ((C (lastQueue N hN i)).length+1) from fun m => departure_weight N hN C ⟨i,m⟩]
    rw [← Finset.mul_sum, gamma_sum_fin N hN _ _ (by omega), mul_one]
  rw [ha, ht, hd, ← add_assoc, sum_arrival_transfer]
  unfold Lambda
  ring

set_option backward.isDefEq.respectTransparency false in
include hN in
theorem incoming_hasSum :
    HasSum (fun D => N.netPi D * N.rate D C) (N.netPi C * Lambda N C) := by
  rw [← sum_incomingWeight N hN C]
  exact hasSum_incoming_parameters N hN C

end KellyNetworkProof


open KellyReversibility.Networks

namespace KellyNetworkProof

theorem native_network_equilibrium {I J : ℕ} (N : Network I J) (hN : N.IsValid)
    (hb : ∀ j : Fin J, Summable (fun n : ℕ => N.a j ^ n / N.phiProd j n)) :
    (∀ C : N.State, 0 < N.netPi C) ∧ HasSum N.netPi 1 ∧
      KellyStochasticNetworks.FullBalance N.netPi N.rate := by
  refine ⟨netPi_pos N hN hb, netPi_hasSum N hN hb, ?_⟩
  intro C
  rw [(outgoing_hasSum N hN C).tsum_eq, (incoming_hasSum N hN C).tsum_eq]

end KellyNetworkProof




namespace KellyReversibility.Networks

/-- **Theorem 3.1** (Kelly 1979, p. 61). For an open network of queues with general customer
routes satisfying the constraints of §3.1, if every series `b_j⁻¹ = ∑_n a_j^n / ∏_{l ≤ n} φ_j(l)`
converges, then `π(C) = ∏_j π_j(c_j)` is the equilibrium distribution: it is positive, sums to `1`
over all network states, and satisfies the equilibrium equations for the rates (3.2), (3.4), (3.6). -/
theorem open_network_equilibrium {I J : ℕ} (N : Network I J) (hN : N.IsValid)
    (hb : ∀ j : Fin J, Summable (fun n : ℕ => N.a j ^ n / N.phiProd j n)) :
    (∀ C : N.State, 0 < N.netPi C) ∧ HasSum N.netPi 1 ∧
      KellyStochasticNetworks.FullBalance N.netPi N.rate := by
  exact KellyNetworkProof.native_network_equilibrium N hN hb

end KellyReversibility.Networks

open KellyReversibility.Networks

theorem solution {I J : ℕ} (N : Network I J) (hN : N.IsValid)
    (hb : ∀ j : Fin J, Summable (fun n : ℕ => N.a j ^ n / N.phiProd j n)) :
    (∀ C : N.State, 0 < N.netPi C) ∧ HasSum N.netPi 1 ∧
      KellyStochasticNetworks.FullBalance N.netPi N.rate := KellyReversibility.Networks.open_network_equilibrium N hN hb

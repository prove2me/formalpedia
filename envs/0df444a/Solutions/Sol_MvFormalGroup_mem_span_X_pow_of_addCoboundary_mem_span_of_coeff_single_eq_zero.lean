-- Prove2me | solution 1 for MvFormalGroup.mem_span_X_pow_of_addCoboundary_mem_span_of_coeff_single_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/5df41989-10c9-54de-be00-19df9a055cbd

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_FormalGroup_NSeries
import Theorems.Thm_MvPowerSeries_coeff_sumElim_single_subst_add_sum_X_mul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_mem_span_X_pow_of_addCoboundary_mem_span_of_coeff_single_eq_zero

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace P2mOSPrim

universe u

section MonIdeal

variable {R : Type*} [CommRing R] {σ : Type*}

theorem coeff_eq_zero_of_mem_span_X_pow [Fintype σ] (p : ℕ) {f : MvPowerSeries σ R}
    (hf : f ∈ Ideal.span (Set.range fun s : σ => (X s : MvPowerSeries σ R) ^ p))
    (d : σ →₀ ℕ) (hd : ∀ s, d s < p) : coeff d f = 0 := by
  classical
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hf
  rw [map_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  have hdvd : (X s : MvPowerSeries σ R) ^ p ∣ c s * X s ^ p := dvd_mul_left _ _
  exact (X_pow_dvd_iff.mp hdvd) d (hd s)

theorem exists_eq_sum_X_pow_mul [DecidableEq σ] (p : ℕ) (T : Finset σ) :
    ∀ f : MvPowerSeries σ R, (∀ d : σ →₀ ℕ, (∀ s ∈ T, d s < p) → coeff d f = 0) →
      ∃ q : σ → MvPowerSeries σ R, f = ∑ s ∈ T, X s ^ p * q s := by
  induction T using Finset.induction_on with
  | empty =>
    intro f hf
    refine ⟨fun _ => 0, ?_⟩
    rw [Finset.sum_empty]
    ext d
    rw [map_zero]
    exact hf d (fun s hs => absurd hs (Finset.notMem_empty s))
  | @insert s T hs ih =>
    intro f hf
    let f₀ : MvPowerSeries σ R := fun d => if d s < p then coeff d f else 0
    have hf₀ : ∀ d, coeff d f₀ = if d s < p then coeff d f else 0 := fun d => rfl
    have hdvd : (X s : MvPowerSeries σ R) ^ p ∣ f - f₀ := by
      rw [X_pow_dvd_iff]
      intro d hd
      rw [map_sub, hf₀, if_pos hd, sub_self]
    obtain ⟨q', hq'⟩ := hdvd
    obtain ⟨q, hq⟩ := ih f₀ (by
      intro d hd
      rw [hf₀]
      split_ifs with hds
      · exact hf d (fun t ht => by
          rcases Finset.mem_insert.mp ht with rfl | ht
          · exact hds
          · exact hd t ht)
      · rfl)
    refine ⟨Function.update q s q', ?_⟩
    rw [Finset.sum_insert hs, Function.update_self]
    have hrest : ∑ t ∈ T, X t ^ p * Function.update q s q' t = ∑ t ∈ T, X t ^ p * q t := by
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [Function.update_of_ne (ne_of_mem_of_not_mem ht hs)]
    rw [hrest, ← hq, ← hq']
    ring

theorem mem_span_X_pow_of_coeff_eq_zero [Fintype σ] [DecidableEq σ] (p : ℕ) {f : MvPowerSeries σ R}
    (hf : ∀ d : σ →₀ ℕ, (∀ s, d s < p) → coeff d f = 0) :
    f ∈ Ideal.span (Set.range fun s : σ => (X s : MvPowerSeries σ R) ^ p) := by
  obtain ⟨q, hq⟩ := exists_eq_sum_X_pow_mul p Finset.univ f
    (fun d hd => hf d fun s => hd s (Finset.mem_univ s))
  rw [hq]
  exact Ideal.sum_mem _ fun s _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨s, rfl⟩)

end MonIdeal

section CongrW

variable {R : Type*} [CommRing R] {τ : Type*} (ν : (τ →₀ ℕ) →+ ℕ)

theorem coeff_pow_congrW {c c' : MvPowerSeries τ R} {N : ℕ}
    (h : ∀ e : τ →₀ ℕ, ν e ≤ N → coeff e c = coeff e c') {m : ℕ}
    {d : τ →₀ ℕ} (hd : ν d ≤ N) :
    coeff d (c ^ m) = coeff d (c' ^ m) := by
  classical
  induction m generalizing d with
  | zero => rfl
  | succ m IH =>
    rw [pow_succ, pow_succ, coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    have h1 : ν q.1 ≤ N := by
      refine le_trans ?_ hd
      rw [← hq, map_add]
      exact Nat.le_add_right _ _
    have h2 : ν q.2 ≤ N := by
      refine le_trans ?_ hd
      rw [← hq, map_add]
      exact Nat.le_add_left _ _
    rw [IH h1, h q.2 h2]

theorem coeff_finsuppProd_pow_congrW {σ' : Type*} {c c' : σ' → MvPowerSeries τ R} {N : ℕ}
    (h : ∀ j, ∀ e : τ →₀ ℕ, ν e ≤ N → coeff e (c j) = coeff e (c' j))
    (m : σ' →₀ ℕ) {d : τ →₀ ℕ} (hd : ν d ≤ N) :
    coeff d (m.prod fun j l => c j ^ l) = coeff d (m.prod fun j l => c' j ^ l) := by
  classical
  induction m using Finsupp.induction generalizing d with
  | zero => simp
  | single_add j l m hjm hl IH =>
    rw [Finsupp.prod_add_index (fun _ _ => pow_zero _) (fun _ _ _ _ => pow_add _ _ _),
      Finsupp.prod_add_index (fun _ _ => pow_zero _) (fun _ _ _ _ => pow_add _ _ _),
      Finsupp.prod_single_index (h := fun j' l' => c j' ^ l') (pow_zero _),
      Finsupp.prod_single_index (h := fun j' l' => c' j' ^ l') (pow_zero _),
      coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    have h1 : ν q.1 ≤ N := by
      refine le_trans ?_ hd
      rw [← hq, map_add]
      exact Nat.le_add_right _ _
    have h2 : ν q.2 ≤ N := by
      refine le_trans ?_ hd
      rw [← hq, map_add]
      exact Nat.le_add_left _ _
    rw [coeff_pow_congrW ν (h j) h1, IH h2]

theorem coeff_subst_congrW {σ' : Type*} [Finite σ'] {c c' : σ' → MvPowerSeries τ R}
    (hc : ∀ j, (c j).constantCoeff = 0) (hc' : ∀ j, (c' j).constantCoeff = 0) {N : ℕ}
    (h : ∀ j, ∀ e : τ →₀ ℕ, ν e ≤ N → coeff e (c j) = coeff e (c' j))
    (f : MvPowerSeries σ' R) {d : τ →₀ ℕ} (hd : ν d ≤ N) :
    coeff d (subst c f) = coeff d (subst c' f) := by
  rw [coeff_subst (hasSubst_of_constantCoeff_zero hc),
    coeff_subst (hasSubst_of_constantCoeff_zero hc')]
  exact finsum_congr fun m => by
    rw [coeff_finsuppProd_pow_congrW ν h m hd]

end CongrW

section KillY

variable {R : Type*} [CommRing R] {α β : Type*}

open MvPowerSeries.WithPiTopology in

theorem coeff_subst_elim_X_zero [Fintype α] [Fintype β] (f : MvPowerSeries (α ⊕ β) R) (m : α →₀ ℕ) :
    coeff m (subst (Sum.elim (fun a => (X a : MvPowerSeries α R)) fun _ => 0) f) =
      coeff (m.sumElim 0) f := by
  classical
  letI : UniformSpace R := ⊥
  let e : α ↪ α ⊕ β := Function.Embedding.inl
  have hcont : Continuous (killCompl (R := R) e) := by
    apply continuous_pi
    intro d
    exact continuous_coeff (R := R) (Finsupp.embDomain e d)
  have hfam : (fun s : α ⊕ β => killCompl (R := R) e (X s)) =
      Sum.elim (fun a => (X a : MvPowerSeries α R)) fun _ => 0 := by
    funext s
    rcases s with a | b
    · exact killCompl_X (e := e) a
    · refine killCompl_X_eq_zero ?_
      rintro ⟨a, ha⟩
      exact Sum.inl_ne_inr ha
  have hs : HasSubst (Sum.elim (fun a => (X a : MvPowerSeries α R)) fun (_ : β) => (0 : MvPowerSeries α R)) :=
    hasSubst_of_constantCoeff_zero (by rintro (a | b) <;> simp [constantCoeff_X])
  have key := aeval_unique hcont
  have haev : ∀ {a b : α ⊕ β → MvPowerSeries α R} (ha : HasEval a) (hb : HasEval b),
      a = b → (aeval (R := R) ha : MvPowerSeries (α ⊕ β) R →ₐ[R] MvPowerSeries α R) = aeval (R := R) hb := by
    rintro a b ha hb rfl
    rfl
  have hAlg : ⇑(substAlgHom hs) = ⇑(killCompl (R := R) e) := by
    rw [substAlgHom_eq_aeval, haev hs.hasEval (HasEval.X.map hcont) hfam.symm, key]
  have : subst (Sum.elim (fun a => (X a : MvPowerSeries α R)) fun _ => 0) f = killCompl e f := by
    rw [← coe_substAlgHom hs, hAlg]
  rw [this, coeff_killCompl]
  show coeff (Finsupp.embDomain Function.Embedding.inl m) f = _
  rw [Finsupp.embDomain_inl]

end KillY

section TwoBlock

variable {R : Type*} [CommRing R] {n : ℕ}

def nuY (n : ℕ) : (Fin n ⊕ Fin n →₀ ℕ) →+ ℕ where
  toFun e := Finsupp.degree (Finsupp.sumFinsuppAddEquivProdFinsupp e).2
  map_zero' := by simp
  map_add' a b := by
    show Finsupp.degree (Finsupp.sumFinsuppAddEquivProdFinsupp (a + b)).2 =
      Finsupp.degree (Finsupp.sumFinsuppAddEquivProdFinsupp a).2 +
        Finsupp.degree (Finsupp.sumFinsuppAddEquivProdFinsupp b).2
    rw [map_add, Prod.snd_add, map_add]

theorem nuY_sumElim (m y : Fin n →₀ ℕ) : nuY n (m.sumElim y) = Finsupp.degree y := by
  show Finsupp.degree (Finsupp.sumFinsuppAddEquivProdFinsupp (m.sumElim y)).2 = _
  congr 1
  ext κ
  rw [Finsupp.snd_sumFinsuppAddEquivProdFinsupp, Finsupp.sumElim_inr]

theorem eq_sumElim (e : Fin n ⊕ Fin n →₀ ℕ) :
    e = ((Finsupp.sumFinsuppAddEquivProdFinsupp e).1).sumElim (Finsupp.sumFinsuppAddEquivProdFinsupp e).2 := by
  ext s
  rcases s with a | b
  · rw [Finsupp.sumElim_inl, Finsupp.fst_sumFinsuppAddEquivProdFinsupp]
  · rw [Finsupp.sumElim_inr, Finsupp.snd_sumFinsuppAddEquivProdFinsupp]

theorem nuY_le_one (e : Fin n ⊕ Fin n →₀ ℕ) (he : nuY n e ≤ 1) :
    ∃ m : Fin n →₀ ℕ, e = m.sumElim 0 ∨ ∃ κ, e = m.sumElim (Finsupp.single κ 1) := by
  refine ⟨(Finsupp.sumFinsuppAddEquivProdFinsupp e).1, ?_⟩
  set y := (Finsupp.sumFinsuppAddEquivProdFinsupp e).2 with hy
  have hdeg : Finsupp.degree y ≤ 1 := he
  rcases Nat.lt_or_ge (Finsupp.degree y) 1 with h0 | h1
  · left
    have : y = 0 := (Finsupp.degree_eq_zero_iff y).mp (by omega)
    rw [← this]
    exact eq_sumElim e
  · right
    have h1' : Finsupp.degree y = 1 := le_antisymm hdeg h1
    obtain ⟨κ, hκ⟩ : ∃ κ, Finsupp.single κ 1 = y := by
      have hmem : y ∈ {d : Fin n →₀ ℕ | d.degree = 1} := h1'
      rw [← Finsupp.range_single_one] at hmem
      exact hmem
    refine ⟨κ, ?_⟩
    rw [hκ]
    exact eq_sumElim e

theorem coeff_sumElim_subst_XL (q : MvPowerSeries (Fin n) R) (m y : Fin n →₀ ℕ) :
    coeff (m.sumElim y) (subst (fun t => (X (Sum.inl t) : MvPowerSeries (Fin n ⊕ Fin n) R)) q) =
      if y = 0 then coeff m q else 0 := by
  classical
  have hren : subst (fun t => (X (Sum.inl t) : MvPowerSeries (Fin n ⊕ Fin n) R)) q =
      rename (Sum.inl : Fin n → Fin n ⊕ Fin n) q := by
    rw [rename_eq_subst]
    rfl
  rw [hren]
  split_ifs with hy
  · rw [hy, ← Finsupp.embDomain_inl]
    exact coeff_embDomain_rename (Function.Embedding.inl) q m
  · apply coeff_rename_eq_zero
    rintro ⟨d, hd⟩
    apply hy
    ext κ
    have := congrArg (fun f => f (Sum.inr κ)) hd
    simp only [Finsupp.sumElim_inr] at this
    rw [← this, Finsupp.mapDomain_notin_range]
    · rfl
    · rintro ⟨a, ha⟩
      exact Sum.inl_ne_inr ha

theorem coeff_sumElim_subst_XR (q : MvPowerSeries (Fin n) R) (m y : Fin n →₀ ℕ) :
    coeff (m.sumElim y) (subst (fun t => (X (Sum.inr t) : MvPowerSeries (Fin n ⊕ Fin n) R)) q) =
      if m = 0 then coeff y q else 0 := by
  classical
  have hren : subst (fun t => (X (Sum.inr t) : MvPowerSeries (Fin n ⊕ Fin n) R)) q =
      rename (Sum.inr : Fin n → Fin n ⊕ Fin n) q := by
    rw [rename_eq_subst]
    rfl
  rw [hren]
  split_ifs with hm
  · rw [hm, ← Finsupp.embDomain_inr]
    exact coeff_embDomain_rename (Function.Embedding.inr) q y
  · apply coeff_rename_eq_zero
    rintro ⟨d, hd⟩
    apply hm
    ext a
    have := congrArg (fun f => f (Sum.inl a)) hd
    simp only [Finsupp.sumElim_inl] at this
    rw [← this, Finsupp.mapDomain_notin_range]
    · rfl
    · rintro ⟨b, hb⟩
      exact Sum.inr_ne_inl hb

theorem coeff_sumElim_X_inr_mul (h : MvPowerSeries (Fin n ⊕ Fin n) R) (κ : Fin n) (m y : Fin n →₀ ℕ) :
    coeff (m.sumElim y) ((X (Sum.inr κ) : MvPowerSeries (Fin n ⊕ Fin n) R) * h) =
      if 1 ≤ y κ then coeff (m.sumElim (y - Finsupp.single κ 1)) h else 0 := by
  classical
  rw [show (X (Sum.inr κ) : MvPowerSeries (Fin n ⊕ Fin n) R) = monomial (Finsupp.single (Sum.inr κ) 1) 1
    from rfl, coeff_monomial_mul, one_mul]
  have hle : Finsupp.single (Sum.inr κ : Fin n ⊕ Fin n) 1 ≤ m.sumElim y ↔ 1 ≤ y κ := by
    rw [Finsupp.single_le_iff, Finsupp.sumElim_inr]
  have hsub : m.sumElim y - Finsupp.single (Sum.inr κ : Fin n ⊕ Fin n) 1 =
      m.sumElim (y - Finsupp.single κ 1) := by
    ext s
    rcases s with a | b
    · simp [Finsupp.sumElim_inl, Finsupp.single_apply]
    · simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.sumElim_inr, Finsupp.single_apply,
        Sum.inr.injEq]
  by_cases h1 : 1 ≤ y κ
  · rw [if_pos (hle.mpr h1), if_pos h1, hsub]
  · rw [if_neg (fun h => h1 (hle.mp h)), if_neg h1]

end TwoBlock

section Jac

variable {k : Type u} [Field k] {n : ℕ}

def jac (F : MvFormalGroup n k) (i κ : Fin n) : MvPowerSeries (Fin n) k :=
  fun m => coeff (m.sumElim (Finsupp.single κ 1)) (F.toPowerSeries i)

theorem coeff_jac (F : MvFormalGroup n k) (i κ : Fin n) (m : Fin n →₀ ℕ) :
    coeff m (jac F i κ) = coeff (m.sumElim (Finsupp.single κ 1)) (F.toPowerSeries i) := rfl

theorem constantCoeff_jac (F : MvFormalGroup n k) (i κ : Fin n) :
    constantCoeff (jac F i κ) = if i = κ then 1 else 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_jac, Finsupp.sumElim_zero_single, F.coeff_single_inr]

theorem coeff_sumElim_single_subst_law (F : MvFormalGroup n k) (g : MvPowerSeries (Fin n) k)
    (m : Fin n →₀ ℕ) (κ : Fin n) :
    coeff (m.sumElim (Finsupp.single κ 1)) (subst F.toPowerSeries g) =
      coeff m (∑ i, jac F i κ * MvPowerSeries.pderivLin i g) := by
  classical
  let T : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k := fun i =>
    subst (fun t => (X (Sum.inl t) : MvPowerSeries (Fin n ⊕ Fin n) k)) ((X : Fin n → MvPowerSeries (Fin n) k) i) +
      ∑ κ : Fin n, X (Sum.inr κ) *
        subst (fun t => (X (Sum.inl t) : MvPowerSeries (Fin n ⊕ Fin n) k)) (jac F i κ)
  have hT0 : ∀ i m, coeff (m.sumElim 0) (T i) = coeff m (X i : MvPowerSeries (Fin n) k) := by
    intro i m
    show coeff (m.sumElim 0) (subst _ (X i) + ∑ κ : Fin n, X (Sum.inr κ) * subst _ (jac F i κ)) = _
    rw [map_add, map_sum, coeff_sumElim_subst_XL, if_pos rfl]
    rw [Finset.sum_eq_zero fun κ _ => ?_, add_zero]
    rw [coeff_sumElim_X_inr_mul, if_neg (by simp)]
  have hT1 : ∀ i m κ, coeff (m.sumElim (Finsupp.single κ 1)) (T i) = coeff m (jac F i κ) := by
    intro i m κ
    show coeff (m.sumElim (Finsupp.single κ 1))
      (subst _ (X i) + ∑ κ' : Fin n, X (Sum.inr κ') * subst _ (jac F i κ')) = _
    rw [map_add, map_sum, coeff_sumElim_subst_XL, if_neg (Finsupp.single_ne_zero.mpr one_ne_zero),
      zero_add, Finset.sum_eq_single κ]
    · rw [coeff_sumElim_X_inr_mul, if_pos (by simp), tsub_self, coeff_sumElim_subst_XL, if_pos rfl]
    · intro κ' _ hne
      rw [coeff_sumElim_X_inr_mul, if_neg (by rw [Finsupp.single_apply, if_neg hne.symm]; omega)]
    · intro h
      exact absurd (Finset.mem_univ κ) h
  have hF0 : ∀ i m, coeff (m.sumElim 0) (F.toPowerSeries i) = coeff m (X i : MvPowerSeries (Fin n) k) := by
    intro i m
    rw [← coeff_subst_elim_X_zero (F.toPowerSeries i) m, MvFormalGroup.subst_elim_X_zero F i]
  have hcongr : ∀ i e, nuY n e ≤ 1 → coeff e (F.toPowerSeries i) = coeff e (T i) := by
    intro i e he
    obtain ⟨m, h⟩ := nuY_le_one e he
    rcases h with rfl | ⟨κ, rfl⟩
    · rw [hF0, hT0]
    · rw [hT1, coeff_jac]
  have hT0c : ∀ i, (T i).constantCoeff = 0 := by
    intro i
    rw [← coeff_zero_eq_constantCoeff_apply, show (0 : Fin n ⊕ Fin n →₀ ℕ) = (0 : Fin n →₀ ℕ).sumElim 0
      from Finsupp.sumElim_zero_zero.symm, hT0, coeff_zero_eq_constantCoeff_apply, constantCoeff_X]
  have hDf : ∀ (i : Fin n) (m : Fin n →₀ ℕ), coeff m (MvPowerSeries.pderivLin i g) =
      ((m i + 1 : ℕ) : k) * coeff (m + Finsupp.single i 1) g := by
    intro i m
    rw [MvPowerSeries.kw_coeff_pderiv, nsmul_eq_mul]
  rw [coeff_subst_congrW (nuY n) F.constantCoeff_eq_zero hT0c (N := 1) hcongr g
    (by rw [nuY_sumElim, Finsupp.degree_single])]
  have h := MvPowerSeries.coeff_sumElim_single_subst_add_sum_X_mul_eq g
    (fun i => MvPowerSeries.pderivLin i g) hDf (X : Fin n → MvPowerSeries (Fin n) k)
    (fun i => constantCoeff_X i) (jac F) m κ
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show subst (X : Fin n → MvPowerSeries (Fin n) k) (MvPowerSeries.pderivLin i g) =
    MvPowerSeries.pderivLin i g from congrFun subst_self _]

theorem mem_of_jac_mul_mem (F : MvFormalGroup n k) (𝔞 : Ideal (MvPowerSeries (Fin n) k))
    (D : Fin n → MvPowerSeries (Fin n) k) (hV : ∀ κ, (∑ i, jac F i κ * D i) ∈ 𝔞) :
    ∀ i, D i ∈ 𝔞 := by
  classical
  let M : Matrix (Fin n) (Fin n) (MvPowerSeries (Fin n) k) := fun κ i => jac F i κ
  have hMD : ∀ κ, (M.mulVec D) κ = ∑ i, jac F i κ * D i := fun κ => rfl
  have hM0 : M.map (constantCoeff : MvPowerSeries (Fin n) k →+* k) = 1 := by
    ext κ i
    rw [Matrix.map_apply, Matrix.one_apply]
    show constantCoeff (jac F i κ) = _
    rw [constantCoeff_jac]
    simp only [eq_comm]
  have hdet : IsUnit M.det := by
    rw [isUnit_iff_constantCoeff]
    have : constantCoeff M.det = 1 := by
      rw [show constantCoeff M.det = (constantCoeff : MvPowerSeries (Fin n) k →+* k) M.det from rfl,
        RingHom.map_det, RingHom.mapMatrix_apply, hM0, Matrix.det_one]
    rw [this]
    exact isUnit_one
  intro i
  have h1 : (M.adjugate.mulVec (M.mulVec D)) i = M.det * D i := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    rfl
  have h2 : (M.adjugate.mulVec (M.mulVec D)) i ∈ 𝔞 := by
    show (∑ κ, M.adjugate i κ * (M.mulVec D) κ) ∈ 𝔞
    exact Ideal.sum_mem _ fun κ _ => Ideal.mul_mem_left _ _ (by rw [hMD]; exact hV κ)
  rw [h1] at h2
  obtain ⟨u, hu⟩ := hdet
  have : D i = ↑u⁻¹ * (M.det * D i) := by
    rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
  rw [this]
  exact Ideal.mul_mem_left _ _ h2

theorem coeff_eq_zero_of_pderiv (p : ℕ) [Fact p.Prime] [CharP k p] (g : MvPowerSeries (Fin n) k)
    (d : Fin n →₀ ℕ) (i : Fin n) (hi : ¬ p ∣ d i)
    (h : coeff (d - Finsupp.single i 1) (MvPowerSeries.pderivLin i g) = 0) :
    coeff d g = 0 := by
  have hi0 : d i ≠ 0 := fun h0 => hi (h0 ▸ dvd_zero p)
  have hle : Finsupp.single i 1 ≤ d := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi0)
  have hmd : d - Finsupp.single i 1 + Finsupp.single i 1 = d := tsub_add_cancel_of_le hle
  rw [MvPowerSeries.kw_coeff_pderiv, nsmul_eq_mul, hmd] at h
  have hmi : ((d - Finsupp.single i 1 : Fin n →₀ ℕ) i) + 1 = d i := by
    have := congrArg (fun f => f i) hmd
    simpa [Finsupp.add_apply, Finsupp.single_apply] using this
  rw [hmi] at h
  have hne : ((d i : ℕ) : k) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff k p]
    exact hi
  exact (mul_eq_zero.mp h).resolve_left hne

end Jac

section Main

variable {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] {n : ℕ}

theorem prim_frob_ker (F : MvFormalGroup n k)
    (g : MvPowerSeries (Fin n) k) (hg0 : MvPowerSeries.constantCoeff g = 0)
    (hglin : ∀ m, MvPowerSeries.coeff (Finsupp.single m 1) g = 0)
    (hprim : F.addCoboundary g ∈ Ideal.span (Set.range fun s : Fin n ⊕ Fin n =>
      (MvPowerSeries.X s : MvPowerSeries (Fin n ⊕ Fin n) k) ^ p)) :
    g ∈ Ideal.span (Set.range fun i : Fin n => (MvPowerSeries.X i : MvPowerSeries (Fin n) k) ^ p) := by
  classical
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le

  have hcob : ∀ m κ, coeff (m.sumElim (Finsupp.single κ 1)) (F.addCoboundary g) =
      coeff m (∑ i, jac F i κ * MvPowerSeries.pderivLin i g) := by
    intro m κ
    unfold MvFormalGroup.addCoboundary
    rw [map_sub, map_sub, coeff_sumElim_single_subst_law, coeff_sumElim_subst_XL,
      if_neg (Finsupp.single_ne_zero.mpr one_ne_zero), sub_zero, coeff_sumElim_subst_XR]
    split_ifs with hm
    · rw [hglin, sub_zero]
    · rw [sub_zero]
  have hV : ∀ κ, (∑ i, jac F i κ * MvPowerSeries.pderivLin i g) ∈
      Ideal.span (Set.range fun i : Fin n => (MvPowerSeries.X i : MvPowerSeries (Fin n) k) ^ p) := by
    intro κ
    apply mem_span_X_pow_of_coeff_eq_zero
    intro m hm
    rw [← hcob]
    apply coeff_eq_zero_of_mem_span_X_pow p hprim
    rintro (a | b)
    · rw [Finsupp.sumElim_inl]; exact hm a
    · rw [Finsupp.sumElim_inr, Finsupp.single_apply]
      split_ifs <;> omega
  have hD := mem_of_jac_mul_mem F _ _ hV
  apply mem_span_X_pow_of_coeff_eq_zero
  intro d hd
  by_cases hd0 : d = 0
  · rw [hd0, coeff_zero_eq_constantCoeff_apply, hg0]
  · obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hd0 (Finsupp.ext hc)
    have hndvd : ¬ p ∣ d i := fun hdvd =>
      absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hi) hdvd) (not_le.mpr (hd i))
    refine coeff_eq_zero_of_pderiv p g d i hndvd ?_
    exact coeff_eq_zero_of_mem_span_X_pow p (hD i) _ (fun s => lt_of_le_of_lt tsub_le_self (hd s))

theorem factor_frob (F : MvFormalGroup n k)
    (φ : Fin n → MvPowerSeries (Fin n) k) (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hφF : ∀ i, MvPowerSeries.subst F.toPowerSeries (φ i) =
      MvPowerSeries.subst
        (Sum.elim
          (fun j => MvPowerSeries.subst
            (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (φ j))
          fun j => MvPowerSeries.subst
            (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (φ j))
        (F.toPowerSeries i))
    (hlin : MvFormalGroup.linearPart φ = 0) :
    ∃ ψ : Fin n → MvPowerSeries (Fin n) k, (∀ i, MvPowerSeries.constantCoeff (ψ i) = 0) ∧
      ∀ i, φ i = MvPowerSeries.subst (fun j => (MvPowerSeries.X j : MvPowerSeries (Fin n) k) ^ p) (ψ i) := by
  classical
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hlin' : ∀ j κ, coeff (Finsupp.single κ 1) (φ j) = 0 := by
    intro j κ
    have := congrFun (congrFun hlin j) κ
    simpa [MvFormalGroup.linearPart, Matrix.of_apply] using this

  have hinL0 : ∀ j, (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (φ j)).constantCoeff = 0 :=
    fun j => constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
      (fun _ => constantCoeff_X _) (hφ0 j)
  have hinR0 : ∀ j, (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (φ j)).constantCoeff = 0 :=
    fun j => constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
      (fun _ => constantCoeff_X _) (hφ0 j)
  have hc0 : ∀ s, ((Sum.elim
      (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (φ j))
      fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (φ j)) s).constantCoeff = 0 := by
    rintro (j | j)
    · exact hinL0 j
    · exact hinR0 j
  have hc0' : ∀ s, ((Sum.elim
      (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (φ j))
      fun (_ : Fin n) => (0 : MvPowerSeries (Fin n ⊕ Fin n) k)) s).constantCoeff = 0 := by
    rintro (j | j)
    · exact hinL0 j
    · exact map_zero _
  have hagree : ∀ s, ∀ e : Fin n ⊕ Fin n →₀ ℕ, nuY n e ≤ 1 →
      coeff e ((Sum.elim
        (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (φ j))
        fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (φ j)) s) =
      coeff e ((Sum.elim
        (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (φ j))
        fun (_ : Fin n) => (0 : MvPowerSeries (Fin n ⊕ Fin n) k)) s) := by
    rintro (j | j) e he
    · rfl
    · show coeff e (subst _ (φ j)) = coeff e 0
      rw [map_zero]
      obtain ⟨m, h⟩ := nuY_le_one e he
      rcases h with rfl | ⟨κ, rfl⟩
      · rw [coeff_sumElim_subst_XR]
        split_ifs
        · rw [coeff_zero_eq_constantCoeff_apply, hφ0]
        · rfl
      · rw [coeff_sumElim_subst_XR]
        split_ifs
        · exact hlin' j κ
        · rfl
  have hRHS : ∀ (j : Fin n) (m : Fin n →₀ ℕ) (κ : Fin n), coeff (m.sumElim (Finsupp.single κ 1)) (subst (Sum.elim
      (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (φ j))
      fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (φ j))
      (F.toPowerSeries j)) = 0 := by
    intro j m κ
    rw [coeff_subst_congrW (nuY n) hc0 hc0' (N := 1) hagree (F.toPowerSeries j)
      (by rw [nuY_sumElim, Finsupp.degree_single]),
      MvFormalGroup.subst_elim_zero_right F hinL0 j, coeff_sumElim_subst_XL,
      if_neg (Finsupp.single_ne_zero.mpr one_ne_zero)]

  have hV : ∀ j κ, (∑ i, jac F i κ * MvPowerSeries.pderivLin i (φ j)) ∈ (⊥ : Ideal (MvPowerSeries (Fin n) k)) := by
    intro j κ
    rw [Ideal.mem_bot]
    ext m
    rw [map_zero, ← coeff_sumElim_single_subst_law, hφF j, hRHS]
  have hD : ∀ j i, MvPowerSeries.pderivLin i (φ j) = 0 := fun j i =>
    (Ideal.mem_bot).mp (mem_of_jac_mul_mem F ⊥ _ (hV j) i)
  have hcoeff : ∀ j d (i : Fin n), ¬ p ∣ d i → coeff d (φ j) = 0 := fun j d i hi =>
    coeff_eq_zero_of_pderiv p (φ j) d i hi (by rw [hD, map_zero])

  refine ⟨fun j => fun e => coeff (p • e) (φ j), fun j => ?_, fun j => ?_⟩
  · show coeff (p • (0 : Fin n →₀ ℕ)) (φ j) = 0
    rw [smul_zero, coeff_zero_eq_constantCoeff_apply, hφ0]
  · rw [← substAlgHom_apply (HasSubst.X_pow hp0), ← MvPowerSeries.expand]
    ext m
    by_cases h : ∀ i, p ∣ m i
    · choose e he using h
      have hm : m = p • (Finsupp.equivFunOnFinite.symm e : Fin n →₀ ℕ) := by
        ext i
        rw [Finsupp.smul_apply, smul_eq_mul]
        show m i = p * e i
        exact he i
      rw [hm, coeff_expand_smul]
      rfl
    · push Not at h
      obtain ⟨i, hi⟩ := h
      rw [coeff_expand_of_not_dvd p hp0 _ hi, hcoeff j m i hi]
    exact hp0

end Main

end P2mOSPrim

end

universe u

theorem solution
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] {n : ℕ} (F : MvFormalGroup n k)
    (g : MvPowerSeries (Fin n) k) (hg0 : MvPowerSeries.constantCoeff g = 0)
    (hglin : ∀ m, MvPowerSeries.coeff (Finsupp.single m 1) g = 0)
    (hprim : F.addCoboundary g ∈ Ideal.span (Set.range fun s : Fin n ⊕ Fin n =>
      (MvPowerSeries.X s : MvPowerSeries (Fin n ⊕ Fin n) k) ^ p)) :
    g ∈ Ideal.span (Set.range fun i : Fin n => (MvPowerSeries.X i : MvPowerSeries (Fin n) k) ^ p) := by
  exact P2mOSPrim.prim_frob_ker p F g hg0 hglin hprim

end S_MvFormalGroup_mem_span_X_pow_of_addCoboundary_mem_span_of_coeff_single_eq_zero
end P2MW
export P2MW.S_MvFormalGroup_mem_span_X_pow_of_addCoboundary_mem_span_of_coeff_single_eq_zero (solution)

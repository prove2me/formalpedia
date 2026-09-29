-- Prove2me | solution 1 for MvFormalGroup.cartierDual_pow_apply_eq_finsum_coeff_subst_mul_apply_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/0cd8065a-8f11-505f-ab8e-8acfd69369c7

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_cartierDual_pow_apply_eq_finsum_coeff_subst_mul_apply_pow

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u v

noncomputable section

open MvPowerSeries
open scoped TensorProduct

namespace P2mFV

section Toolkit

variable {k : Type u} [CommRing k]

def box (ι : Type*) [Finite ι] [DecidableEq ι] (N : ℕ) : Finset (ι →₀ ℕ) :=
  Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ => N)

theorem mem_box {ι : Type*} [Finite ι] [DecidableEq ι] {N : ℕ} {c : ι →₀ ℕ} :
    c ∈ box ι N ↔ ∀ i, c i ≤ N := by
  rw [box, Finset.mem_Iic, Finsupp.le_def]
  refine forall_congr' fun i => ?_
  rw [Finsupp.coe_equivFunOnFinite_symm]

theorem mem_box_of_degree_le {ι : Type*} [Finite ι] [DecidableEq ι] {N : ℕ} {c : ι →₀ ℕ}
    (h : c.degree ≤ N) : c ∈ box ι N :=
  mem_box.mpr fun i => (Finsupp.le_degree i c).trans h

theorem lt_degree_of_not_mem_box {ι : Type*} [Finite ι] [DecidableEq ι] {N : ℕ} {c : ι →₀ ℕ}
    (h : c ∉ box ι N) : N < c.degree := by
  rw [mem_box] at h
  push Not at h
  obtain ⟨i, hi⟩ := h
  exact lt_of_lt_of_le hi (Finsupp.le_degree i c)

theorem box_mono {ι : Type*} [Finite ι] [DecidableEq ι] {N N' : ℕ} (h : N ≤ N') :
    box ι N ⊆ box ι N' := by
  intro c hc
  rw [mem_box] at hc ⊢
  exact fun i => (hc i).trans h

theorem sumElim_mem_box_iff {α β : Type*} [Finite α] [Finite β] [DecidableEq α] [DecidableEq β]
    {N : ℕ} {x : α →₀ ℕ} {y : β →₀ ℕ} :
    x.sumElim y ∈ box (α ⊕ β) N ↔ x ∈ box α N ∧ y ∈ box β N := by
  simp only [mem_box]
  constructor
  · intro h
    exact ⟨fun i => h (Sum.inl i), fun j => h (Sum.inr j)⟩
  · rintro ⟨h1, h2⟩ (i | j)
    · exact h1 i
    · exact h2 j

theorem degree_sumElim {α β : Type*} (x : α →₀ ℕ) (y : β →₀ ℕ) :
    (x.sumElim y).degree = x.degree + y.degree := by
  classical
  rw [Finsupp.sumElim_eq_add, map_add, Finsupp.degree_mapDomain, Finsupp.degree_mapDomain]

theorem sum_box_sum {α β : Type*} [Finite α] [Finite β] [DecidableEq α] [DecidableEq β]
    {M : Type*} [AddCommMonoid M] (N : ℕ)
    (f : (α ⊕ β →₀ ℕ) → M) :
    ∑ c ∈ box (α ⊕ β) N, f c = ∑ x ∈ box α N, ∑ y ∈ box β N, f (x.sumElim y) := by
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_equiv (Finsupp.sumFinsuppAddEquivProdFinsupp (α := α) (β := β)).symm.toEquiv ?_ ?_
  · rintro ⟨x, y⟩
    rw [Finset.mem_product]
    show x ∈ box α N ∧ y ∈ box β N ↔ Finsupp.sumFinsuppAddEquivProdFinsupp.symm (x, y) ∈ box (α ⊕ β) N
    rw [Finsupp.sumFinsuppAddEquivProdFinsupp_symm_apply, sumElim_mem_box_iff]
  · rintro ⟨x, y⟩ _
    rfl

theorem coeff_finsuppProd_pow_eq_zero_of_degree_lt {ι τ : Type*} {σ : ι → MvPowerSeries τ k}
    (hσ : ∀ t, constantCoeff (σ t) = 0) {c : ι →₀ ℕ} {e : τ →₀ ℕ} (h : e.degree < c.degree) :
    coeff e (c.prod fun t m => σ t ^ m) = 0 := by
  refine coeff_of_lt_order (lt_of_lt_of_le ?_ (MvFormalGroup.le_order_finsuppProd_pow hσ c))
  exact_mod_cast h

theorem coeff_subst_eq_sum {ι τ : Type*} [Finite ι] {σ : ι → MvPowerSeries τ k}
    (hσ : ∀ t, constantCoeff (σ t) = 0) (f : MvPowerSeries ι k) (e : τ →₀ ℕ)
    (T : Finset (ι →₀ ℕ)) (hT : ∀ c : ι →₀ ℕ, c.degree ≤ e.degree → c ∈ T) :
    coeff e (subst σ f) = ∑ c ∈ T, coeff c f * coeff e (c.prod fun t m => σ t ^ m) := by
  rw [coeff_subst (hasSubst_of_constantCoeff_zero hσ)]
  refine finsum_eq_sum_of_support_subset _ fun c hc => ?_
  rw [Finset.mem_coe]
  by_contra hcT
  apply hc
  have hlt : e.degree < c.degree := by
    by_contra hle
    exact hcT (hT c (not_lt.mp hle))
  show coeff c f • coeff e (c.prod fun t m => σ t ^ m) = 0
  rw [coeff_finsuppProd_pow_eq_zero_of_degree_lt hσ hlt, smul_zero]

theorem coeff_subst_eq_sum_box {ι τ : Type*} [Finite ι] [DecidableEq ι] {σ : ι → MvPowerSeries τ k}
    (hσ : ∀ t, constantCoeff (σ t) = 0) (f : MvPowerSeries ι k) (e : τ →₀ ℕ)
    {N : ℕ} (hN : e.degree ≤ N) :
    coeff e (subst σ f) = ∑ c ∈ box ι N, coeff c f * coeff e (c.prod fun t m => σ t ^ m) :=
  coeff_subst_eq_sum hσ f e _ fun c hc => mem_box_of_degree_le (hc.trans hN)

theorem coeff_subst_eq_sum_box₂ {α β τ : Type*} [Finite α] [Finite β] [DecidableEq α] [DecidableEq β]
    {σ : α ⊕ β → MvPowerSeries τ k}
    (hσ : ∀ t, constantCoeff (σ t) = 0) (f : MvPowerSeries (α ⊕ β) k) (e : τ →₀ ℕ)
    {N : ℕ} (hN : e.degree ≤ N) :
    coeff e (subst σ f) = ∑ x ∈ box α N, ∑ y ∈ box β N, coeff (x.sumElim y) f *
      coeff e ((x.prod fun j m => σ (Sum.inl j) ^ m) * (y.prod fun j m => σ (Sum.inr j) ^ m)) := by
  rw [coeff_subst_eq_sum_box hσ f e hN, sum_box_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [Finsupp.prod_sumElim]
  rfl

theorem prod_X_pow_eq_monomial {ι : Type*} (e : ι →₀ ℕ) :
    (e.prod fun s m => (X s : MvPowerSeries ι k) ^ m) = monomial e 1 :=
  (monomial_one_eq e).symm

theorem rename_inl_eq_subst {α β : Type*} [Finite α] (f : MvPowerSeries α k) :
    rename (Sum.inl : α → α ⊕ β) f = subst (fun j => (X (Sum.inl j) : MvPowerSeries (α ⊕ β) k)) f :=
  rename_eq_subst _ f

theorem rename_inr_eq_subst {α β : Type*} [Finite β] (f : MvPowerSeries β k) :
    rename (Sum.inr : β → α ⊕ β) f = subst (fun j => (X (Sum.inr j) : MvPowerSeries (α ⊕ β) k)) f :=
  rename_eq_subst _ f

theorem coeff_sumElim_rename_inl {α β : Type*} [Finite α] [DecidableEq β]
    (f : MvPowerSeries α k) (x : α →₀ ℕ) (y : β →₀ ℕ) :
    coeff (x.sumElim y) (rename (Sum.inl : α → α ⊕ β) f) = if y = 0 then coeff x f else 0 := by
  classical
  split_ifs with hy
  · rw [hy, ← Finsupp.embDomain_inl]
    exact coeff_embDomain_rename Function.Embedding.inl f x
  · refine coeff_rename_eq_zero _ _ fun ⟨z, hz⟩ => hy ?_
    ext j
    have h := DFunLike.congr_fun hz (Sum.inr j)
    rw [Finsupp.sumElim_inr, Finsupp.mapDomain_notin_range] at h
    · exact h.symm
    · rintro ⟨i, hi⟩
      exact Sum.inl_ne_inr hi

theorem coeff_sumElim_rename_inr {α β : Type*} [Finite β] [DecidableEq α]
    (f : MvPowerSeries β k) (x : α →₀ ℕ) (y : β →₀ ℕ) :
    coeff (x.sumElim y) (rename (Sum.inr : β → α ⊕ β) f) = if x = 0 then coeff y f else 0 := by
  classical
  split_ifs with hx
  · rw [hx, ← Finsupp.embDomain_inr]
    exact coeff_embDomain_rename Function.Embedding.inr f y
  · refine coeff_rename_eq_zero _ _ fun ⟨z, hz⟩ => hx ?_
    ext j
    have h := DFunLike.congr_fun hz (Sum.inl j)
    rw [Finsupp.sumElim_inl, Finsupp.mapDomain_notin_range] at h
    · exact h.symm
    · rintro ⟨i, hi⟩
      exact Sum.inr_ne_inl hi

theorem coeff_sumElim_rename_inl_mul {α β : Type*} [Finite α] [DecidableEq α] [DecidableEq β]
    (f : MvPowerSeries α k) (H : MvPowerSeries (α ⊕ β) k) (s : α →₀ ℕ) (b : β →₀ ℕ) :
    coeff (s.sumElim b) (rename (Sum.inl : α → α ⊕ β) f * H) =
      ∑ q ∈ Finset.HasAntidiagonal.antidiagonal s, coeff q.1 f * coeff (q.2.sumElim b) H := by
  classical
  rw [coeff_mul]

  let ψ : (α →₀ ℕ) × (α →₀ ℕ) ↪ (α ⊕ β →₀ ℕ) × (α ⊕ β →₀ ℕ) :=
    ⟨fun q => (q.1.sumElim 0, q.2.sumElim b), fun q q' h => by
      obtain ⟨h1, h2⟩ := Prod.mk.inj h
      ext i
      · have := DFunLike.congr_fun h1 (Sum.inl i)
        simpa only [Finsupp.sumElim_inl] using this
      · have := DFunLike.congr_fun h2 (Sum.inl i)
        simpa only [Finsupp.sumElim_inl] using this⟩
  have hψ : ∀ q, ψ q = (q.1.sumElim 0, q.2.sumElim b) := fun q => rfl
  have himage : (Finset.HasAntidiagonal.antidiagonal s).map ψ ⊆ Finset.HasAntidiagonal.antidiagonal (s.sumElim b) := by
    intro m hm
    rw [Finset.mem_map] at hm
    obtain ⟨q, hq, rfl⟩ := hm
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq ⊢
    rw [hψ, ← Finsupp.sumElim_add, hq, zero_add]
  rw [← Finset.sum_subset himage, Finset.sum_map]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [hψ, coeff_sumElim_rename_inl, if_pos rfl]
  · rintro ⟨m₁, m₂⟩ hm hnot
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hm

    obtain ⟨x₁, y₁, rfl⟩ : ∃ x₁ y₁, m₁ = Finsupp.sumElim x₁ y₁ :=
      ⟨_, _, (Finsupp.comapDomain_sumElim_comapDomain m₁).symm⟩
    obtain ⟨x₂, y₂, rfl⟩ : ∃ x₂ y₂, m₂ = Finsupp.sumElim x₂ y₂ :=
      ⟨_, _, (Finsupp.comapDomain_sumElim_comapDomain m₂).symm⟩
    by_cases hy₁ : y₁ = 0
    · exfalso
      apply hnot
      rw [Finset.mem_map]
      rw [← Finsupp.sumElim_add] at hm
      have hx : x₁ + x₂ = s := by
        ext i
        have := DFunLike.congr_fun hm (Sum.inl i)
        simpa only [Finsupp.sumElim_inl] using this
      have hy : y₁ + y₂ = b := by
        ext j
        have := DFunLike.congr_fun hm (Sum.inr j)
        simpa only [Finsupp.sumElim_inr] using this
      rw [hy₁, zero_add] at hy
      refine ⟨(x₁, x₂), Finset.HasAntidiagonal.mem_antidiagonal.mpr hx, ?_⟩
      rw [hψ, hy₁, hy]
    · show coeff (x₁.sumElim y₁) _ * _ = 0
      rw [coeff_sumElim_rename_inl, if_neg hy₁, zero_mul]

theorem coeff_sumElim_rename_inl_mul_rename_inr {α β : Type*} [Finite α] [Finite β]
    [DecidableEq α] [DecidableEq β]
    (f : MvPowerSeries α k) (h : MvPowerSeries β k) (s : α →₀ ℕ) (b : β →₀ ℕ) :
    coeff (s.sumElim b) (rename (Sum.inl : α → α ⊕ β) f * rename (Sum.inr : β → α ⊕ β) h) =
      coeff s f * coeff b h := by
  rw [coeff_sumElim_rename_inl_mul, Finset.sum_eq_single (s, 0)]
  · rw [coeff_sumElim_rename_inr, if_pos rfl]
  · rintro ⟨q₁, q₂⟩ hq hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    have hq2 : q₂ ≠ 0 := by
      intro hzero
      apply hne
      simp only [hzero, add_zero] at hq
      rw [hq, hzero]
    rw [coeff_sumElim_rename_inr, if_neg hq2, mul_zero]
  · intro h
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (add_zero s)) h

theorem finsuppProd_pow_rename {α ι τ : Type*} (e : ι → τ) [Filter.TendstoCofinite e]
    (u : α → MvPowerSeries ι k) (x : α →₀ ℕ) :
    (x.prod fun j m => rename e (u j) ^ m) = rename e (x.prod fun j m => u j ^ m) := by
  rw [map_finsuppProd]
  simp only [map_pow]

end Toolkit

section Operators

variable {k : Type u} [CommRing k] {n : ℕ}

def rowX (a : Fin n →₀ ℕ) : MvPowerSeries (Fin n ⊕ Fin n) k →ₗ[k] MvPowerSeries (Fin n) k where
  toFun H := fun b => coeff (a.sumElim b) H
  map_add' H H' := by
    funext b
    exact map_add _ H H'
  map_smul' c H := by
    funext b
    exact map_smul _ c H

theorem coeff_rowX (a b : Fin n →₀ ℕ) (H : MvPowerSeries (Fin n ⊕ Fin n) k) :
    coeff b (rowX a H) = coeff (a.sumElim b) H := rfl

def D (F : MvFormalGroup n k) (a : Fin n →₀ ℕ) : MvPowerSeries (Fin n) k →ₗ[k] MvPowerSeries (Fin n) k :=
  rowX a ∘ₗ (substAlgHom F.hasSubst_toPowerSeries).toLinearMap

theorem coeff_D (F : MvFormalGroup n k) (a b : Fin n →₀ ℕ) (G : MvPowerSeries (Fin n) k) :
    coeff b (D F a G) = coeff (a.sumElim b) (subst F.toPowerSeries G) := by
  show coeff (a.sumElim b) (substAlgHom F.hasSubst_toPowerSeries G) = _
  rw [substAlgHom_apply]

def Fpow (F : MvFormalGroup n k) (c : Fin n →₀ ℕ) : MvPowerSeries (Fin n ⊕ Fin n) k :=
  c.prod fun j m => F.toPowerSeries j ^ m

theorem coeff_D_eq_sum (F : MvFormalGroup n k) (a b : Fin n →₀ ℕ) (G : MvPowerSeries (Fin n) k)
    {N : ℕ} (hN : a.degree + b.degree ≤ N) :
    coeff b (D F a G) = ∑ c ∈ box (Fin n) N, coeff c G * coeff (a.sumElim b) (Fpow F c) := by
  rw [coeff_D, coeff_subst_eq_sum_box (N := N) F.constantCoeff_eq_zero G _
    (by rw [degree_sumElim]; exact hN)]
  rfl

end Operators

section Comm

variable {k : Type u} [CommRing k] {n : ℕ} (F : MvFormalGroup n k)

def FYZ (j : Fin n) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k :=
  rename (Sum.inr : Fin n ⊕ Fin n → Fin n ⊕ (Fin n ⊕ Fin n)) (F.toPowerSeries j)

def θ₁ : Fin n ⊕ Fin n → MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k :=
  Sum.elim (fun j => X (Sum.inl j)) (FYZ F)

theorem constantCoeff_θ₁ : ∀ t, constantCoeff (θ₁ F t) = 0 := by
  rintro (j | j)
  · exact constantCoeff_X _
  · show constantCoeff (rename _ (F.toPowerSeries j)) = 0
    rw [constantCoeff_rename, F.constantCoeff_eq_zero]

def τ₁ (j : Fin n) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k :=
  subst (θ₁ F) (F.toPowerSeries j)

theorem constantCoeff_τ₁ (j : Fin n) : constantCoeff (τ₁ F j) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (constantCoeff_θ₁ F))
    (constantCoeff_θ₁ F) (F.constantCoeff_eq_zero j)

theorem subst_τ₁ (G : MvPowerSeries (Fin n) k) :
    subst (τ₁ F) G = subst (θ₁ F) (subst F.toPowerSeries G) := by
  rw [subst_comp_subst_apply F.hasSubst_toPowerSeries
    (hasSubst_of_constantCoeff_zero (constantCoeff_θ₁ F))]
  rfl

theorem prod_X_inl_pow (x : Fin n →₀ ℕ) :
    (x.prod fun j m => (X (Sum.inl j) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k) ^ m) =
      rename (Sum.inl : Fin n → Fin n ⊕ (Fin n ⊕ Fin n)) (monomial x (1 : k)) := by
  rw [← prod_X_pow_eq_monomial, map_finsuppProd]
  simp only [map_pow, rename_X]

theorem coeff_subst_τ₁ (G : MvPowerSeries (Fin n) k) (a b c : Fin n →₀ ℕ) :
    coeff (a.sumElim (b.sumElim c)) (subst (τ₁ F) G) = coeff c (D F b (D F a G)) := by
  have hN : (a.sumElim (b.sumElim c)).degree ≤ a.degree + b.degree + c.degree := by
    rw [degree_sumElim, degree_sumElim, add_assoc]
  rw [subst_τ₁, coeff_subst_eq_sum_box₂ (constantCoeff_θ₁ F) _ _ hN,
    coeff_D_eq_sum (N := a.degree + b.degree + c.degree) F b c _ (by omega),
    Finset.sum_eq_single_of_mem a (mem_box_of_degree_le (by omega))]
  · refine Finset.sum_congr rfl fun y _ => ?_
    have h1 : (a.prod fun j m => θ₁ F (Sum.inl j) ^ m) =
        rename (Sum.inl : Fin n → Fin n ⊕ (Fin n ⊕ Fin n)) (monomial a (1 : k)) := prod_X_inl_pow a
    have h2 : (y.prod fun j m => θ₁ F (Sum.inr j) ^ m) =
        rename (Sum.inr : Fin n ⊕ Fin n → Fin n ⊕ (Fin n ⊕ Fin n)) (Fpow F y) :=
      finsuppProd_pow_rename _ _ y
    rw [h1, h2, coeff_sumElim_rename_inl_mul_rename_inr, coeff_monomial, if_pos rfl, one_mul, coeff_D]
  · intro x _ hxa
    apply Finset.sum_eq_zero
    intro y _
    have h1 : (x.prod fun j m => θ₁ F (Sum.inl j) ^ m) =
        rename (Sum.inl : Fin n → Fin n ⊕ (Fin n ⊕ Fin n)) (monomial x (1 : k)) := prod_X_inl_pow x
    have h2 : (y.prod fun j m => θ₁ F (Sum.inr j) ^ m) =
        rename (Sum.inr : Fin n ⊕ Fin n → Fin n ⊕ (Fin n ⊕ Fin n)) (Fpow F y) :=
      finsuppProd_pow_rename _ _ y
    rw [h1, h2, coeff_sumElim_rename_inl_mul_rename_inr, coeff_monomial, if_neg (Ne.symm hxa), zero_mul,
      mul_zero]

def sw : Fin n ⊕ (Fin n ⊕ Fin n) → Fin n ⊕ (Fin n ⊕ Fin n)
  | Sum.inl a => Sum.inr (Sum.inl a)
  | Sum.inr (Sum.inl b) => Sum.inl b
  | Sum.inr (Sum.inr c) => Sum.inr (Sum.inr c)

theorem sw_sw : Function.Involutive (sw (n := n)) := by
  rintro (a | b | c) <;> rfl

def swPerm : Equiv.Perm (Fin n ⊕ (Fin n ⊕ Fin n)) := Function.Involutive.toPerm sw sw_sw

theorem embDomain_swPerm (a b c : Fin n →₀ ℕ) :
    Finsupp.embDomain (swPerm (n := n)).toEmbedding (b.sumElim (a.sumElim c)) = a.sumElim (b.sumElim c) := by
  ext t
  rcases t with (i | i | i)
  · have h : (Sum.inl i : Fin n ⊕ (Fin n ⊕ Fin n)) = (swPerm (n := n)).toEmbedding (Sum.inr (Sum.inl i)) :=
      rfl
    rw [h, Finsupp.embDomain_apply_self]
    rfl
  · have h : (Sum.inr (Sum.inl i) : Fin n ⊕ (Fin n ⊕ Fin n)) =
        (swPerm (n := n)).toEmbedding (Sum.inl i) := rfl
    rw [h, Finsupp.embDomain_apply_self]
    rfl
  · have h : (Sum.inr (Sum.inr i) : Fin n ⊕ (Fin n ⊕ Fin n)) =
        (swPerm (n := n)).toEmbedding (Sum.inr (Sum.inr i)) := rfl
    rw [h, Finsupp.embDomain_apply_self]
    rfl

theorem coeff_rename_sw (P : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k) (a b c : Fin n →₀ ℕ) :
    coeff (a.sumElim (b.sumElim c)) (rename (sw (n := n)) P) = coeff (b.sumElim (a.sumElim c)) P := by
  rw [← embDomain_swPerm]
  exact coeff_embDomain_rename (swPerm (n := n)).toEmbedding P _

theorem rename_sw_τ₁ [F.IsComm] (j : Fin n) : rename (sw (n := n)) (τ₁ F j) = τ₁ F j := by

  let A : Fin n → MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k := fun l => X (Sum.inl l)
  let B : Fin n → MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k := fun l => X (Sum.inr (Sum.inl l))
  let C : Fin n → MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k := fun l => X (Sum.inr (Sum.inr l))
  have hA : ∀ l, constantCoeff (A l) = 0 := fun l => constantCoeff_X _
  have hB : ∀ l, constantCoeff (B l) = 0 := fun l => constantCoeff_X _
  have hC : ∀ l, constantCoeff (C l) = 0 := fun l => constantCoeff_X _
  have hFYZ : ∀ j, FYZ F j = subst (Sum.elim B C) (F.toPowerSeries j) := by
    intro j
    rw [FYZ, rename_eq_subst]
    congr 1
    funext t
    rcases t with (l | l) <;> rfl
  have hθ : θ₁ F = Sum.elim A fun j => subst (Sum.elim B C) (F.toPowerSeries j) := by
    funext t
    rcases t with (l | l)
    · rfl
    · exact hFYZ l

  have hτ : τ₁ F j = subst (Sum.elim B fun j => subst (Sum.elim A C) (F.toPowerSeries j))
      (F.toPowerSeries j) := by
    rw [τ₁, hθ, ← MvFormalGroup.subst_elim_assoc F hA hB hC j]
    have hcomm : (fun j' => subst (Sum.elim A B) (F.toPowerSeries j')) =
        fun j' => subst (Sum.elim B A) (F.toPowerSeries j') :=
      funext fun j' => MvFormalGroup.subst_elim_comm F hA hB j'
    rw [hcomm, MvFormalGroup.subst_elim_assoc F hB hA hC j]

  have hsw : HasSubst (X ∘ sw : Fin n ⊕ (Fin n ⊕ Fin n) → MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k) :=
    HasSubst.X_comp _
  conv_lhs => rw [τ₁, rename_eq_subst,
    subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (constantCoeff_θ₁ F)) hsw]
  rw [hτ]
  congr 1
  funext t
  rcases t with (l | l)
  · show subst (X ∘ sw) (X (Sum.inl l)) = X (Sum.inr (Sum.inl l))
    rw [subst_X hsw]
    rfl
  · show subst (X ∘ sw) (FYZ F l) = subst (Sum.elim A C) (F.toPowerSeries l)
    rw [← rename_eq_subst, FYZ, rename_rename, rename_eq_subst]
    congr 1
    funext t
    rcases t with (l' | l') <;> rfl

theorem D_comm [F.IsComm] (a b : Fin n →₀ ℕ) : D F a ∘ₗ D F b = D F b ∘ₗ D F a := by
  refine LinearMap.ext fun G => ?_
  ext c
  show coeff c (D F a (D F b G)) = coeff c (D F b (D F a G))
  rw [← coeff_subst_τ₁, ← coeff_subst_τ₁, ← coeff_rename_sw (subst (τ₁ F) G) a b c, rename_eq_subst,
    subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (constantCoeff_τ₁ F)) (HasSubst.X_comp _)]
  congr 2
  funext j
  rw [← rename_eq_subst, rename_sw_τ₁]

theorem D_apply_comm [F.IsComm] (a b : Fin n →₀ ℕ) (G : MvPowerSeries (Fin n) k) :
    D F a (D F b G) = D F b (D F a G) :=
  LinearMap.congr_fun (D_comm F a b) G

end Comm

section Iterated

variable {k : Type u} [CommRing k] {n : ℕ} (F : MvFormalGroup n k)

def 𝒜 : Subalgebra k (Module.End k (MvPowerSeries (Fin n) k)) :=
  Algebra.adjoin k (Set.range (D F))

theorem D_mem_𝒜 (a : Fin n →₀ ℕ) : D F a ∈ 𝒜 F := Algebra.subset_adjoin ⟨a, rfl⟩

scoped instance isMulCommutative_𝒜 [F.IsComm] : IsMulCommutative (𝒜 F) :=
  Algebra.isMulCommutative_adjoin k (by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact D_comm F a b)

def genD : MvPowerSeries (Fin n) (𝒜 F) := fun a => ⟨D F a, D_mem_𝒜 F a⟩

theorem coeff_genD (a : Fin n →₀ ℕ) : coeff a (genD F) = ⟨D F a, D_mem_𝒜 F a⟩ := rfl

theorem coe_coeff_genD (a : Fin n →₀ ℕ) :
    ((coeff a (genD F) : 𝒜 F) : Module.End k (MvPowerSeries (Fin n) k)) = D F a := rfl

def Q (m : ℕ) (s : Fin n →₀ ℕ) : Module.End k (MvPowerSeries (Fin n) k) :=
  ((coeff s (genD F ^ m) : 𝒜 F) : Module.End k (MvPowerSeries (Fin n) k))

theorem Q_zero (s : Fin n →₀ ℕ) : Q F 0 s = if s = 0 then 1 else 0 := by
  classical
  rw [Q, pow_zero, coeff_one]
  split_ifs <;> rfl

theorem Q_succ (m : ℕ) (s : Fin n →₀ ℕ) :
    Q F (m + 1) s = ∑ q ∈ Finset.HasAntidiagonal.antidiagonal s, D F q.1 * Q F m q.2 := by
  rw [Q, pow_succ', coeff_mul, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Subalgebra.coe_mul]
  rfl

def nthL (m : ℕ) (j : Fin n) : MvPowerSeries (Fin n ⊕ Fin n) k :=
  rename (Sum.inl : Fin n → Fin n ⊕ Fin n) (F.nthSeries m j)

theorem constantCoeff_nthL (m : ℕ) (j : Fin n) : constantCoeff (nthL F m j) = 0 := by
  rw [nthL, constantCoeff_rename, MvFormalGroup.constantCoeff_nthSeries]

def θD (m : ℕ) : Fin n ⊕ Fin n → MvPowerSeries (Fin n ⊕ Fin n) k :=
  Sum.elim (nthL F m) fun j => X (Sum.inr j)

theorem constantCoeff_θD (m : ℕ) : ∀ t, constantCoeff (θD F m t) = 0 := by
  rintro (j | j)
  · exact constantCoeff_nthL F m j
  · exact constantCoeff_X _

def τD (m : ℕ) (j : Fin n) : MvPowerSeries (Fin n ⊕ Fin n) k :=
  subst (θD F m) (F.toPowerSeries j)

theorem constantCoeff_τD (m : ℕ) (j : Fin n) : constantCoeff (τD F m j) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (constantCoeff_θD F m))
    (constantCoeff_θD F m) (F.constantCoeff_eq_zero j)

theorem subst_τD (m : ℕ) (G : MvPowerSeries (Fin n) k) :
    subst (τD F m) G = subst (θD F m) (subst F.toPowerSeries G) := by
  rw [subst_comp_subst_apply F.hasSubst_toPowerSeries
    (hasSubst_of_constantCoeff_zero (constantCoeff_θD F m))]
  rfl

def θE (m : ℕ) : Fin n ⊕ Fin n → MvPowerSeries (Fin n ⊕ Fin n) k :=
  Sum.elim (nthL F m) F.toPowerSeries

theorem constantCoeff_θE (m : ℕ) : ∀ t, constantCoeff (θE F m t) = 0 := by
  rintro (j | j)
  · exact constantCoeff_nthL F m j
  · exact F.constantCoeff_eq_zero j

theorem τD_zero (j : Fin n) : τD F 0 j = X (Sum.inr j) := by
  have hXr : HasSubst (fun l : Fin n => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) :=
    hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
  have hz : HasSubst (Sum.elim (fun _ : Fin n => (0 : MvPowerSeries (Fin n) k)) fun l => X l) :=
    MvFormalGroup.hasSubst_elim (fun _ => map_zero _) (fun l => constantCoeff_X l)
  have key := congrArg (subst (fun l : Fin n => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)))
    (MvFormalGroup.subst_elim_zero_X F j)
  rw [subst_X hXr, subst_comp_subst_apply hz hXr] at key
  rw [← key, τD]
  congr 1
  funext t
  rcases t with (l | l)
  · show rename Sum.inl (F.nthSeries 0 l) = subst _ 0
    rw [MvFormalGroup.nthSeries_zero, map_zero, ← coe_substAlgHom hXr, map_zero]
  · show X (Sum.inr l) = subst _ (X l)
    rw [subst_X hXr]

theorem nthL_succ (m : ℕ) (j : Fin n) :
    nthL F (m + 1) j = subst (Sum.elim (nthL F m) fun l => X (Sum.inl l)) (F.toPowerSeries j) := by
  have hXl : HasSubst (X ∘ Sum.inl : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k) := HasSubst.X_comp _
  rw [nthL, MvFormalGroup.nthSeries_succ, rename_eq_subst,
    subst_comp_subst_apply (MvFormalGroup.hasSubst_elim (MvFormalGroup.constantCoeff_nthSeries F m)
      (fun l => constantCoeff_X l)) hXl]
  congr 1
  funext t
  rcases t with (l | l)
  · show subst (X ∘ Sum.inl) (F.nthSeries m l) = rename Sum.inl (F.nthSeries m l)
    rw [rename_eq_subst]
  · show subst (X ∘ Sum.inl) (X l) = X (Sum.inl l)
    rw [subst_X hXl]
    rfl

theorem τD_succ (m : ℕ) (j : Fin n) : τD F (m + 1) j = subst (θE F m) (F.toPowerSeries j) := by
  have hXl : ∀ l : Fin n, constantCoeff (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k) = 0 :=
    fun l => constantCoeff_X _
  have hXr : ∀ l : Fin n, constantCoeff (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k) = 0 :=
    fun l => constantCoeff_X _
  have h1 : θD F (m + 1) = Sum.elim (fun j => subst (Sum.elim (nthL F m) fun l => X (Sum.inl l))
      (F.toPowerSeries j)) fun l => X (Sum.inr l) := by
    funext t
    rcases t with (l | l)
    · exact nthL_succ F m l
    · rfl
  rw [τD, h1, MvFormalGroup.subst_elim_assoc F (constantCoeff_nthL F m) hXl hXr j, θE]
  congr 2
  funext l
  have hX : (Sum.elim (fun l => X (Sum.inl l)) fun l => X (Sum.inr l)) =
      (X : Fin n ⊕ Fin n → MvPowerSeries (Fin n ⊕ Fin n) k) := by
    funext t
    rcases t with (l | l) <;> rfl
  rw [hX]
  exact congrFun subst_self _

theorem subst_τD_succ (m : ℕ) (G : MvPowerSeries (Fin n) k) :
    subst (τD F (m + 1)) G = subst (θE F m) (subst F.toPowerSeries G) := by
  rw [subst_comp_subst_apply F.hasSubst_toPowerSeries
    (hasSubst_of_constantCoeff_zero (constantCoeff_θE F m))]
  congr 1
  funext j
  exact τD_succ F m j

def nthPow (m : ℕ) (x : Fin n →₀ ℕ) : MvPowerSeries (Fin n) k :=
  x.prod fun j m' => F.nthSeries m j ^ m'

theorem prod_nthL_pow (m : ℕ) (x : Fin n →₀ ℕ) :
    (x.prod fun j m' => nthL F m j ^ m') = rename (Sum.inl : Fin n → Fin n ⊕ Fin n) (nthPow F m x) :=
  finsuppProd_pow_rename _ _ x

theorem prod_X_inr_pow (y : Fin n →₀ ℕ) :
    (y.prod fun j m => (X (Sum.inr j) : MvPowerSeries (Fin n ⊕ Fin n) k) ^ m) =
      rename (Sum.inr : Fin n → Fin n ⊕ Fin n) (monomial y (1 : k)) := by
  rw [← prod_X_pow_eq_monomial, map_finsuppProd]
  simp only [map_pow, rename_X]

theorem degree_le_of_mem_box {N : ℕ} {y : Fin n →₀ ℕ} (hy : y ∈ box (Fin n) N) : y.degree ≤ n * N := by
  rw [mem_box] at hy
  rw [Finsupp.degree_eq_sum]
  calc ∑ i, y i ≤ ∑ _i : Fin n, N := Finset.sum_le_sum fun i _ => hy i
    _ = n * N := by simp

theorem degree_fst_le_of_mem_antidiagonal {s : Fin n →₀ ℕ} {q : (Fin n →₀ ℕ) × (Fin n →₀ ℕ)}
    (hq : q ∈ Finset.HasAntidiagonal.antidiagonal s) : q.1.degree ≤ s.degree := by
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
  rw [← hq, map_add]
  exact Nat.le_add_right _ _

theorem degree_snd_le_of_mem_antidiagonal {s : Fin n →₀ ℕ} {q : (Fin n →₀ ℕ) × (Fin n →₀ ℕ)}
    (hq : q ∈ Finset.HasAntidiagonal.antidiagonal s) : q.2.degree ≤ s.degree := by
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
  rw [← hq, map_add]
  exact Nat.le_add_left _ _

theorem coeff_subst_τD_eq_sum (m : ℕ) (G : MvPowerSeries (Fin n) k) (s y : Fin n →₀ ℕ) {N : ℕ}
    (hN : s.degree + y.degree ≤ N) :
    coeff (s.sumElim y) (subst (τD F m) G) =
      ∑ x ∈ box (Fin n) N, coeff (x.sumElim y) (subst F.toPowerSeries G) * coeff s (nthPow F m x) := by
  rw [subst_τD, coeff_subst_eq_sum_box₂ (N := N) (constantCoeff_θD F m) _ _
    (by rw [degree_sumElim]; exact hN)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single_of_mem y (mem_box_of_degree_le (le_trans (Nat.le_add_left _ _) hN))]
  · have h1 : (x.prod fun j m' => θD F m (Sum.inl j) ^ m') =
        rename (Sum.inl : Fin n → Fin n ⊕ Fin n) (nthPow F m x) := prod_nthL_pow F m x
    have h2 : (y.prod fun j m' => θD F m (Sum.inr j) ^ m') =
        rename (Sum.inr : Fin n → Fin n ⊕ Fin n) (monomial y (1 : k)) := prod_X_inr_pow y
    rw [h1, h2, coeff_sumElim_rename_inl_mul_rename_inr, coeff_monomial, if_pos rfl, mul_one]
  · intro y' _ hy'
    have h1 : (x.prod fun j m' => θD F m (Sum.inl j) ^ m') =
        rename (Sum.inl : Fin n → Fin n ⊕ Fin n) (nthPow F m x) := prod_nthL_pow F m x
    have h2 : (y'.prod fun j m' => θD F m (Sum.inr j) ^ m') =
        rename (Sum.inr : Fin n → Fin n ⊕ Fin n) (monomial y' (1 : k)) := prod_X_inr_pow y'
    rw [h1, h2, coeff_sumElim_rename_inl_mul_rename_inr, coeff_monomial, if_neg (Ne.symm hy'), mul_zero,
      mul_zero]

theorem coeff_subst_τD [F.IsComm] (m : ℕ) :
    ∀ (G : MvPowerSeries (Fin n) k) (s b : Fin n →₀ ℕ),
      coeff (s.sumElim b) (subst (τD F m) G) = coeff b (Q F m s G) := by
  classical
  induction m with
  | zero =>
    intro G s b
    have h0 : (τD F 0) = fun j => (X (Sum.inr j) : MvPowerSeries (Fin n ⊕ Fin n) k) :=
      funext (τD_zero F)
    rw [h0, ← rename_inr_eq_subst, coeff_sumElim_rename_inr, Q_zero]
    split_ifs
    · rfl
    · rw [LinearMap.zero_apply, map_zero]
  | succ m ih =>
    intro G s b

    set N₀ : ℕ := s.degree + b.degree with hN₀
    obtain ⟨M, hM⟩ : ∃ M, ∀ y ∈ box (Fin n) N₀, y.degree ≤ M :=
      ⟨n * N₀, fun y hy => degree_le_of_mem_box hy⟩
    set N₂ : ℕ := N₀ + M with hN₂
    set K := subst F.toPowerSeries G with hK

    have hL : coeff (s.sumElim b) (subst (τD F (m + 1)) G) =
        ∑ x ∈ box (Fin n) N₂, ∑ y ∈ box (Fin n) N₀, ∑ q ∈ Finset.HasAntidiagonal.antidiagonal s,
          coeff (x.sumElim y) K * (coeff q.1 (nthPow F m x) * coeff (q.2.sumElim b) (Fpow F y)) := by
      rw [subst_τD_succ, coeff_subst_eq_sum_box₂ (N := N₂) (constantCoeff_θE F m) _ _
        (by rw [degree_sumElim]; omega)]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.sum_subset (box_mono (by omega : N₀ ≤ N₂))]
      · refine Finset.sum_congr rfl fun y _ => ?_
        have h1 : (x.prod fun j m' => θE F m (Sum.inl j) ^ m') =
            rename (Sum.inl : Fin n → Fin n ⊕ Fin n) (nthPow F m x) := prod_nthL_pow F m x
        rw [h1, ← Finset.mul_sum, ← coeff_sumElim_rename_inl_mul]
        rfl
      · intro y _ hy
        have h1 : (x.prod fun j m' => θE F m (Sum.inl j) ^ m') =
            rename (Sum.inl : Fin n → Fin n ⊕ Fin n) (nthPow F m x) := prod_nthL_pow F m x
        rw [h1]
        show coeff (x.sumElim y) K * coeff (s.sumElim b) (rename Sum.inl (nthPow F m x) * Fpow F y) = 0
        rw [coeff_sumElim_rename_inl_mul, Finset.sum_eq_zero, mul_zero]
        intro q hq
        rw [Fpow, coeff_finsuppProd_pow_eq_zero_of_degree_lt F.constantCoeff_eq_zero, mul_zero]
        rw [degree_sumElim]
        have h2 := degree_snd_le_of_mem_antidiagonal hq
        have h3 := lt_degree_of_not_mem_box hy
        omega

    have hR : coeff b (Q F (m + 1) s G) =
        ∑ q ∈ Finset.HasAntidiagonal.antidiagonal s, ∑ y ∈ box (Fin n) N₀, ∑ x ∈ box (Fin n) N₂,
          coeff (x.sumElim y) K * (coeff q.2 (nthPow F m x) * coeff (q.1.sumElim b) (Fpow F y)) := by
      rw [Q_succ, LinearMap.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [Module.End.mul_apply, coeff_D_eq_sum (N := N₀) F q.1 b _
        (by have := degree_fst_le_of_mem_antidiagonal hq; omega)]
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [← ih G q.2 y, coeff_subst_τD_eq_sum F m G q.2 y
        (N := N₂) (by have := degree_snd_le_of_mem_antidiagonal hq; have := hM y hy; omega),
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    rw [hL, hR, Finset.sum_comm (β := k) (s := box (Fin n) N₂) (t := box (Fin n) N₀),
      Finset.sum_comm (β := k) (s := Finset.HasAntidiagonal.antidiagonal s) (t := box (Fin n) N₀)]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_comm (β := k) (s := Finset.HasAntidiagonal.antidiagonal s) (t := box (Fin n) N₂)]
    refine Finset.sum_congr rfl fun x _ => ?_
    conv_rhs => rw [← Finset.HasAntidiagonal.map_swap_antidiagonal (n := s), Finset.sum_map]
    rfl

end Iterated

section Frob

variable {k : Type u} [CommRing k] {n : ℕ} (F : MvFormalGroup n k)

theorem algebraMap_𝒜_injective : Function.Injective (algebraMap k (𝒜 F)) := by
  intro c c' h
  have h' := congrArg (fun z : 𝒜 F => constantCoeff ((z : Module.End k (MvPowerSeries (Fin n) k)) 1)) h
  simp only [Subalgebra.coe_algebraMap, Module.algebraMap_end_apply] at h'
  simpa using h'

theorem Q_prime_nsmul [F.IsComm] (p : ℕ) [hp : Fact p.Prime] [CharP k p] (a : Fin n →₀ ℕ) :
    Q F p (p • a) = D F a ^ p := by
  open scoped IsMulCommutative in
  letI : CommRing (𝒜 F) := inferInstance
  haveI : CharP (𝒜 F) p := charP_of_injective_algebraMap (algebraMap_𝒜_injective F) p
  haveI : ExpChar (𝒜 F) p := ExpChar.prime hp.out
  rw [Q, ← map_frobenius_expand p hp.out.ne_zero, coeff_map, coeff_expand_smul, frobenius_def,
    Subalgebra.coe_pow]
  rfl

theorem killCompl_inl_subst {ι : Type*} [Finite ι] (τ : ι → MvPowerSeries (Fin n ⊕ Fin n) k)
    (hτ : ∀ i, constantCoeff (τ i) = 0) (G : MvPowerSeries ι k) :
    killCompl (Function.Embedding.inl : Fin n ↪ Fin n ⊕ Fin n) (subst τ G) =
      subst (fun i => killCompl (Function.Embedding.inl : Fin n ↪ Fin n ⊕ Fin n) (τ i)) G := by
  classical
  have hκτ : ∀ i, constantCoeff (killCompl (Function.Embedding.inl : Fin n ↪ Fin n ⊕ Fin n) (τ i)) = 0 := by
    intro i
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_killCompl, Finsupp.embDomain_zero,
      coeff_zero_eq_constantCoeff_apply, hτ i]
  ext s
  rw [coeff_killCompl, Finsupp.embDomain_inl,
    coeff_subst_eq_sum_box (N := s.degree) hτ G _ (by rw [degree_sumElim, map_zero, add_zero]),
    coeff_subst_eq_sum_box (N := s.degree) hκτ G _ le_rfl]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  rw [← Finsupp.embDomain_inl, ← coeff_killCompl (e := (Function.Embedding.inl : Fin n ↪ Fin n ⊕ Fin n)),
    map_finsuppProd]
  simp only [map_pow]

theorem subst_elim_zero_right {τ : Type*} (u : Fin n → MvPowerSeries τ k)
    (hu : ∀ i, constantCoeff (u i) = 0) (j : Fin n) :
    subst (Sum.elim u fun _ => (0 : MvPowerSeries τ k)) (F.toPowerSeries j) = u j := by
  have hsu : HasSubst u := hasSubst_of_constantCoeff_zero hu
  have hz : HasSubst (Sum.elim (fun l => (X l : MvPowerSeries (Fin n) k)) fun _ => 0) :=
    MvFormalGroup.hasSubst_elim (fun l => constantCoeff_X l) (fun _ => map_zero _)
  have key := congrArg (subst u) (MvFormalGroup.subst_elim_X_zero F j)
  rw [subst_X hsu, subst_comp_subst_apply hz hsu] at key
  rw [← key]
  congr 1
  funext t
  rcases t with (l | l)
  · show u l = subst u (X l)
    rw [subst_X hsu]
  · show 0 = subst u 0
    rw [← coe_substAlgHom hsu, map_zero]

theorem killCompl_inl_τD (m : ℕ) (j : Fin n) :
    killCompl (Function.Embedding.inl : Fin n ↪ Fin n ⊕ Fin n) (τD F m j) = F.nthSeries m j := by
  rw [τD, killCompl_inl_subst _ (constantCoeff_θD F m)]
  have hfam : (fun t => killCompl (Function.Embedding.inl : Fin n ↪ Fin n ⊕ Fin n) (θD F m t)) =
      Sum.elim (F.nthSeries m) fun _ => 0 := by
    funext t
    rcases t with (l | l)
    · exact killCompl_rename_app (e := (Function.Embedding.inl : Fin n ↪ Fin n ⊕ Fin n)) _
    · refine killCompl_X_eq_zero ?_
      rintro ⟨i, hi⟩
      exact Sum.inl_ne_inr hi
  rw [hfam, subst_elim_zero_right F _ (MvFormalGroup.constantCoeff_nthSeries F m) j]

theorem coeff_sumElim_zero_subst_τD (m : ℕ) (G : MvPowerSeries (Fin n) k) (s : Fin n →₀ ℕ) :
    coeff (s.sumElim 0) (subst (τD F m) G) = coeff s (subst (F.nthSeries m) G) := by
  rw [← Finsupp.embDomain_inl, ← coeff_killCompl (e := (Function.Embedding.inl : Fin n ↪ Fin n ⊕ Fin n)),
    killCompl_inl_subst _ (constantCoeff_τD F m)]
  congr 2
  funext j
  exact killCompl_inl_τD F m j

theorem constantCoeff_D_pow_apply [F.IsComm] (p : ℕ) [Fact p.Prime] [CharP k p] (a : Fin n →₀ ℕ)
    (g : MvPowerSeries (Fin n) k) :
    constantCoeff ((D F a ^ p) g) = coeff (p • a) (subst (F.nthSeries p) g) := by
  rw [← Q_prime_nsmul, ← coeff_zero_eq_constantCoeff_apply, ← coeff_subst_τD F p g (p • a) 0,
    coeff_sumElim_zero_subst_τD]

theorem coeff_nsmul_subst_nthSeries (p : ℕ) (hp : p ≠ 0)
    (V : Fin n → MvPowerSeries (Fin n) k) (hV0 : ∀ i, constantCoeff (V i) = 0)
    (hV : ∀ i, subst (fun l => (X l : MvPowerSeries (Fin n) k) ^ p) (V i) = F.nthSeries p i)
    (a : Fin n →₀ ℕ) (g : MvPowerSeries (Fin n) k) :
    coeff (p • a) (subst (F.nthSeries p) g) = coeff a (subst V g) := by
  have hV' : (F.nthSeries p) = fun i => expand p hp (V i) := by
    funext i
    rw [← hV i, expand, substAlgHom_apply]
  rw [hV', ← expand_subst p hp (hasSubst_of_constantCoeff_zero hV0), coeff_expand_smul]

end Frob

section Assembly

variable {k : Type u} [CommRing k] {n : ℕ} (F : MvFormalGroup n k)

theorem constantCoeff_iterate_eq (p : ℕ) [hp : Fact p.Prime] [CharP k p] [F.IsComm]
    (V : Fin n → MvPowerSeries (Fin n) k) (hV0 : ∀ i, constantCoeff (V i) = 0)
    (hV : ∀ i, subst (fun l => (X l : MvPowerSeries (Fin n) k) ^ p) (V i) = F.nthSeries p i)
    (S : Finset (Fin n →₀ ℕ)) (w : (Fin n →₀ ℕ) → k)
    (E : MvPowerSeries (Fin n) k → MvPowerSeries (Fin n) k)
    (hE : ∀ (G : MvPowerSeries (Fin n) k) (b : Fin n →₀ ℕ), coeff b (E G) =
      ∑ a ∈ S, w a * coeff (a.sumElim b) (subst F.toPowerSeries G))
    (g : MvPowerSeries (Fin n) k) :
    constantCoeff (E^[p] g) = ∑ a ∈ S, w a ^ p * coeff a (subst V g) := by

  let e𝒜 : 𝒜 F := ∑ a ∈ S, w a • ⟨D F a, D_mem_𝒜 F a⟩
  have hEe : E = ⇑((e𝒜 : 𝒜 F) : Module.End k (MvPowerSeries (Fin n) k)) := by
    funext G
    ext b
    rw [hE, AddSubmonoidClass.coe_finsetSum, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Subalgebra.coe_smul, LinearMap.smul_apply, map_smul, smul_eq_mul, coeff_D]

  have hpow : ((e𝒜 ^ p : 𝒜 F) : Module.End k (MvPowerSeries (Fin n) k)) =
      ∑ a ∈ S, w a ^ p • D F a ^ p := by
    open scoped IsMulCommutative in
    letI : CommRing (𝒜 F) := inferInstance
    haveI : CharP (𝒜 F) p := charP_of_injective_algebraMap (algebraMap_𝒜_injective F) p
    haveI : ExpChar (𝒜 F) p := ExpChar.prime hp.out
    have h1 : e𝒜 ^ p = ∑ a ∈ S, w a ^ p • (⟨D F a, D_mem_𝒜 F a⟩ : 𝒜 F) ^ p := by
      rw [sum_pow_char p]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [smul_pow]
    rw [h1, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Subalgebra.coe_smul, Subalgebra.coe_pow]
  rw [hEe, ← Module.End.pow_apply, ← Subalgebra.coe_pow, hpow, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [LinearMap.smul_apply, ← coeff_zero_eq_constantCoeff_apply, map_smul, smul_eq_mul,
    coeff_zero_eq_constantCoeff_apply, constantCoeff_D_pow_apply,
    coeff_nsmul_subst_nthSeries F p hp.out.ne_zero V hV0 hV]

end Assembly

section Hopf

variable {k : Type u} [Field k] {n : ℕ}

theorem exists_ker_constantCoeff_pow_le (J : Ideal (MvPowerSeries (Fin n) k))
    [Module.Finite k (MvPowerSeries (Fin n) k ⧸ J)] :
    ∃ N : ℕ, 0 < N ∧ (RingHom.ker (constantCoeff : MvPowerSeries (Fin n) k →+* k)) ^ N ≤ J := by
  haveI : IsArtinianRing (MvPowerSeries (Fin n) k ⧸ J) := IsArtinianRing.of_finite k _
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := MvPowerSeries (Fin n) k ⧸ J)
  set mX : Ideal (MvPowerSeries (Fin n) k) := RingHom.ker (constantCoeff : MvPowerSeries (Fin n) k →+* k)
  have hle : Ideal.map (Ideal.Quotient.mk J) mX ≤ Ideal.jacobson (⊥ : Ideal (MvPowerSeries (Fin n) k ⧸ J)) := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_jacobson_bot]
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul, ← map_one (Ideal.Quotient.mk J), ← map_add]
    refine IsUnit.map _ ?_
    rw [isUnit_iff_constantCoeff, map_add, map_mul, RingHom.mem_ker.mp hx, zero_mul, zero_add, map_one]
    exact isUnit_one
  refine ⟨N + 1, Nat.succ_pos N, ?_⟩
  have h1 : Ideal.map (Ideal.Quotient.mk J) (mX ^ (N + 1)) = ⊥ := by
    rw [Ideal.map_pow, eq_bot_iff, pow_succ]
    calc (Ideal.map (Ideal.Quotient.mk J) mX) ^ N * Ideal.map (Ideal.Quotient.mk J) mX
        ≤ (Ideal.jacobson ⊥) ^ N * ⊤ := Ideal.mul_mono (Ideal.pow_right_mono hle N) le_top
      _ = ⊥ := by rw [hN, Ideal.zero_eq_bot, Ideal.bot_mul]
  rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at h1
  exact h1

theorem exists_pow_X_eq_zero {L : Type v} [CommRing L] [Algebra k L] [Module.Finite k L]
    (π : MvPowerSeries (Fin n) k →ₐ[k] L) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ j : Fin n, π (X j) ^ N = 0 := by
  haveI : Module.Finite k π.range :=
    Module.Finite.of_injective (Subalgebra.val π.range).toLinearMap Subtype.val_injective
  haveI : Module.Finite k (MvPowerSeries (Fin n) k ⧸ RingHom.ker π) :=
    Module.Finite.equiv (Ideal.quotientKerEquivRange π).symm.toLinearEquiv
  obtain ⟨N, hN, hle⟩ := exists_ker_constantCoeff_pow_le (RingHom.ker π)
  refine ⟨N, hN, fun j => ?_⟩
  have hX : (X j : MvPowerSeries (Fin n) k) ∈ RingHom.ker (constantCoeff : MvPowerSeries (Fin n) k →+* k) := by
    rw [RingHom.mem_ker, constantCoeff_X]
  have h := hle (Ideal.pow_mem_pow hX N)
  rw [RingHom.mem_ker, map_pow] at h
  exact h

theorem mem_span_X_pow {ι : Type*} [DecidableEq ι] (N : ℕ) (T : Finset ι) :
    ∀ f : MvPowerSeries ι k, (∀ e : ι →₀ ℕ, (∀ s ∈ T, e s < N) → coeff e f = 0) →
      f ∈ Ideal.span ((fun s => (X s : MvPowerSeries ι k) ^ N) '' (T : Set ι)) := by
  induction T using Finset.induction_on with
  | empty =>
    intro f hf
    have : f = 0 := by
      ext e
      rw [coeff_zero]
      exact hf e (fun s hs => absurd hs (Finset.notMem_empty s))
    rw [this]
    exact zero_mem _
  | insert s₀ T hs₀ ih =>
    intro f hf
    let f₀ : MvPowerSeries ι k := fun e => if e s₀ < N then coeff e f else 0
    have hf₀ : ∀ e, coeff e f₀ = if e s₀ < N then coeff e f else 0 := fun e => rfl
    have h1 : (X s₀ : MvPowerSeries ι k) ^ N ∣ f - f₀ := by
      rw [X_pow_dvd_iff]
      intro m hm
      rw [map_sub, hf₀, if_pos hm, sub_self]
    have h2 : f₀ ∈ Ideal.span ((fun s => (X s : MvPowerSeries ι k) ^ N) '' (T : Set ι)) := by
      refine ih f₀ fun e he => ?_
      rw [hf₀]
      by_cases h : e s₀ < N
      · rw [if_pos h]
        refine hf e fun s hs => ?_
        rcases Finset.mem_insert.1 hs with rfl | hs
        · exact h
        · exact he s hs
      · rw [if_neg h]
    have h3 : Ideal.span ((fun s => (X s : MvPowerSeries ι k) ^ N) '' (T : Set ι)) ≤
        Ideal.span ((fun s => (X s : MvPowerSeries ι k) ^ N) '' ((insert s₀ T : Finset ι) : Set ι)) :=
      Ideal.span_mono (Set.image_mono (by simp))
    obtain ⟨g, hg⟩ := h1
    have : f = f₀ + (X s₀ : MvPowerSeries ι k) ^ N * g := by rw [← hg]; ring
    rw [this]
    refine Ideal.add_mem _ (h3 h2) (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨s₀, by simp, rfl⟩))

theorem algHom_eq_sum_box {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Type*} [Ring A] [Algebra k A]
    (ψ : MvPowerSeries ι k →ₐ[k] A) {N : ℕ} (hN : 1 ≤ N) (hψ : ∀ s, ψ (X s) ^ N = 0)
    (H : MvPowerSeries ι k) :
    ψ H = ∑ e ∈ box ι (N - 1), coeff e H • ψ (monomial e (1 : k)) := by
  have hbox : ∀ e : ι →₀ ℕ, e ∈ box ι (N - 1) ↔ ∀ s, e s < N := by
    intro e
    rw [mem_box]
    refine forall_congr' fun s => ?_
    omega
  have hrem : H - ∑ e ∈ box ι (N - 1), coeff e H • monomial e (1 : k) ∈
      Ideal.span ((fun s => (X s : MvPowerSeries ι k) ^ N) '' ((Finset.univ : Finset ι) : Set ι)) := by
    refine mem_span_X_pow N Finset.univ _ fun e he => ?_
    rw [map_sub, map_sum, Finset.sum_eq_single_of_mem e ((hbox e).mpr fun s => he s (Finset.mem_univ s))]
    · rw [map_smul, coeff_monomial, if_pos rfl, smul_eq_mul, mul_one, sub_self]
    · intro e' _ hne
      rw [map_smul, coeff_monomial, if_neg (Ne.symm hne), smul_zero]
  have hker : Ideal.span ((fun s => (X s : MvPowerSeries ι k) ^ N) '' ((Finset.univ : Finset ι) : Set ι)) ≤
      RingHom.ker ψ := by
    rw [Ideal.span_le]
    rintro _ ⟨s, -, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    show ψ (X s ^ N) = 0
    rw [map_pow, hψ]
  have h := hker hrem
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_smul]

theorem monomial_sumElim (x y : Fin n →₀ ℕ) :
    monomial (x.sumElim y) (1 : k) =
      rename (Sum.inl : Fin n → Fin n ⊕ Fin n) (monomial x (1 : k)) *
        rename (Sum.inr : Fin n → Fin n ⊕ Fin n) (monomial y (1 : k)) := by
  rw [rename_monomial, rename_monomial, monomial_mul_monomial, one_mul, ← Finsupp.sumElim_eq_add]

variable {L : Type v} [CommRing L] [HopfAlgebra k L]

def ρ (φ : CartierDual k L) : L →ₗ[k] L :=
  (TensorProduct.lid k L).toLinearMap ∘ₗ (CartierDual.toDual k L φ).rTensor L ∘ₗ Coalgebra.comul

theorem ρ_apply (φ : CartierDual k L) (a : L) :
    ρ φ a = TensorProduct.lid k L ((CartierDual.toDual k L φ).rTensor L (Coalgebra.comul (R := k) a)) := rfl

theorem mul_apply_eq (φ ψ : CartierDual k L) (a : L) : (φ * ψ) a = ψ (ρ φ a) := by
  rw [CartierDual.mul_apply, ρ_apply]
  induction (Coalgebra.comul (R := k) a) using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [TensorProduct.dualDistrib_apply, CartierDual.toDual_apply, CartierDual.toDual_apply,
      LinearMap.rTensor_tmul, TensorProduct.lid_tmul, CartierDual.toDual_apply, map_smul, smul_eq_mul]
  | add s t hs ht => rw [map_add, hs, map_add, map_add, map_add, ht]

theorem pow_apply_eq_counit_iterate (φ : CartierDual k L) (m : ℕ) :
    ∀ a : L, (φ ^ m) a = Coalgebra.counit (R := k) ((ρ φ)^[m] a) := by
  induction m with
  | zero => intro a; rw [pow_zero, CartierDual.one_apply, Function.iterate_zero_apply]
  | succ m ih => intro a; rw [pow_succ', mul_apply_eq, ih, ← Function.iterate_succ_apply]

end Hopf

end P2mFV
p2m_reactivate "P2MW.S_MvFormalGroup_cartierDual_pow_apply_eq_finsum_coeff_subst_mul_apply_pow.P2mFV"

open P2mFV in

theorem solution
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {n : ℕ} (F : MvFormalGroup n k) [F.IsComm]
    (V : Fin n → MvPowerSeries (Fin n) k) (hV0 : ∀ i, MvPowerSeries.constantCoeff (V i) = 0)
    (hV : ∀ i, MvPowerSeries.subst (fun l => (MvPowerSeries.X l : MvPowerSeries (Fin n) k) ^ p) (V i) =
      F.nthSeries p i)
    {L : Type v} [CommRing L] [HopfAlgebra k L] [Module.Finite k L]
    (π : MvPowerSeries (Fin n) k →ₐ[k] L)
    (Θ : MvPowerSeries (Fin n ⊕ Fin n) k →ₐ[k] L ⊗[k] L)
    (hΘl : ∀ G : MvPowerSeries (Fin n) k, Θ (MvPowerSeries.subst
      (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) G) = π G ⊗ₜ[k] 1)
    (hΘr : ∀ G : MvPowerSeries (Fin n) k, Θ (MvPowerSeries.subst
      (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) G) = 1 ⊗ₜ[k] π G)
    (hcomul : ∀ G, Coalgebra.comul (R := k) (π G) = Θ (MvPowerSeries.subst F.toPowerSeries G))
    (hcounit : ∀ G, Coalgebra.counit (R := k) (π G) = MvPowerSeries.constantCoeff G)
    (φ : CartierDual k L) (g : MvPowerSeries (Fin n) k) :
    (φ ^ p) (π g) = ∑ᶠ a : Fin n →₀ ℕ,
      MvPowerSeries.coeff a (MvPowerSeries.subst V g) * φ (π (MvPowerSeries.monomial a (1 : k))) ^ p := by
  classical
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero

  obtain ⟨N, hN1, hπN⟩ := exists_pow_X_eq_zero π
  have hΘN : ∀ t : Fin n ⊕ Fin n, Θ (X t) ^ N = 0 := by
    have hXl : HasSubst (fun l : Fin n => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) :=
      hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
    have hXr : HasSubst (fun l : Fin n => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) :=
      hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
    rintro (j | j)
    · have h := hΘl (X j)
      rw [subst_X hXl] at h
      rw [h, Algebra.TensorProduct.tmul_pow, hπN, TensorProduct.zero_tmul]
    · have h := hΘr (X j)
      rw [subst_X hXr] at h
      rw [h, Algebra.TensorProduct.tmul_pow, hπN, TensorProduct.tmul_zero]

  set Bx : Finset (Fin n →₀ ℕ) := box (Fin n) (N - 1) with hBx
  set w : (Fin n →₀ ℕ) → k := fun a => φ (π (monomial a (1 : k))) with hw
  let E : MvPowerSeries (Fin n) k → MvPowerSeries (Fin n) k := fun G =>
    fun b => ∑ a ∈ Bx, w a * coeff (a.sumElim b) (subst F.toPowerSeries G)
  have hE : ∀ (G : MvPowerSeries (Fin n) k) (b : Fin n →₀ ℕ), coeff b (E G) =
      ∑ a ∈ Bx, w a * coeff (a.sumElim b) (subst F.toPowerSeries G) := fun G b => rfl

  have hπsum : ∀ G, π G = ∑ b ∈ Bx, coeff b G • π (monomial b (1 : k)) :=
    fun G => algHom_eq_sum_box π hN1 hπN G
  have hΘmon : ∀ x y : Fin n →₀ ℕ, Θ (monomial (x.sumElim y) (1 : k)) =
      π (monomial x (1 : k)) ⊗ₜ[k] π (monomial y (1 : k)) := by
    intro x y
    rw [monomial_sumElim, map_mul, rename_inl_eq_subst, rename_inr_eq_subst, hΘl, hΘr,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

  have hπE : ∀ G, π (E G) = ρ φ (π G) := by
    intro G
    rw [ρ_apply, hcomul, algHom_eq_sum_box Θ hN1 hΘN, map_sum, map_sum, sum_box_sum,
      hπsum (E G), Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hE, Finset.sum_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, map_smul, hΘmon, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, CartierDual.toDual_apply,
      smul_smul, mul_comm]

  have hiter : π (E^[p] g) = (ρ φ)^[p] (π g) := (Function.Semiconj.iterate_right hπE p) g
  rw [pow_apply_eq_counit_iterate, ← hiter, hcounit,
    constantCoeff_iterate_eq F p V hV0 hV Bx w E hE g,
    finsum_eq_sum_of_support_subset (s := Bx)]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_comm]
  · intro a ha
    rw [Finset.mem_coe]
    by_contra hmem
    apply ha

    have hbig : ∃ j, N ≤ a j := by
      by_contra hcon
      push Not at hcon
      exact hmem (mem_box.mpr fun j => by have := hcon j; omega)
    obtain ⟨j, hj⟩ := hbig
    have hdvd : (X j : MvPowerSeries (Fin n) k) ^ N ∣ monomial a (1 : k) := by
      rw [X_pow_dvd_iff]
      intro m hm
      rw [coeff_monomial, if_neg]
      rintro rfl
      omega
    obtain ⟨q, hq⟩ := hdvd
    show coeff a (subst V g) * φ (π (monomial a (1 : k))) ^ p = 0
    rw [hq, map_mul, map_pow, hπN j, zero_mul, map_zero, zero_pow hp0, mul_zero]

end
end S_MvFormalGroup_cartierDual_pow_apply_eq_finsum_coeff_subst_mul_apply_pow
end P2MW
export P2MW.S_MvFormalGroup_cartierDual_pow_apply_eq_finsum_coeff_subst_mul_apply_pow (solution)

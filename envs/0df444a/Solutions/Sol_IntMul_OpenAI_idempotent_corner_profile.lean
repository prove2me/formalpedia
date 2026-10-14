-- Prove2me | solution 1 for IntMul.OpenAI.idempotent_corner_profile
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-12T14:32:29.160363+00:00
-- url     : https://prove2.me/submissions/387dec2b-6668-4125-a677-cff57dec342a

import Mathlib

set_option linter.unusedSimpArgs false
open Matrix Finset

namespace CornerAux

variable {K : Type*} [Field K]


theorem alg {R : Type*} [Ring R] (PL PR c c' u v : R)
    (hLL : PL*PL = PL) (hRR : PR*PR = PR) (hLR : PL*PR = 0) (hRL : PR*PL = 0)
    (hcL : PL*c = c) (hcR : c*PR = c) (hc'R : PR*c' = c') (hc'L : c'*PL = c')
    (hcc' : c*c' = PL) (hc'c : c'*c = PR)
    (hLu : PL*u = -PL) (huL : u*PL = u) (hvR : v*PR = -PR) (hRv : PR*v = v) (hvu : v*u = -c') :
    (1 - c') * (1 - v*(1-PL-PR)) * (1 + (1-PL)*u) * (1 + u*c*v) * (1 + v*(1-PR)) * (1 - c')
      * (1 - (1-PL-PR)*u) = (1-PL-PR) + c ∧
    (1 - (1-PL)*u) * (1 + v*(1-PL-PR)) * (1 + c') * ((1-PL-PR) + c) * (1 + (1-PL-PR)*u)
      * (1 + c') * (1 - v*(1-PR)) = 1 + u*c*v := by
  have hRc : PR*c = 0 := by rw [← hcL, ← mul_assoc, hRL, zero_mul]
  have hcL0 : c*PL = 0 := by rw [← hcR, mul_assoc, hRL, mul_zero]
  have hLc' : PL*c' = 0 := by rw [← hc'R, ← mul_assoc, hLR, zero_mul]
  have hc'R0 : c'*PR = 0 := by rw [← hc'L, mul_assoc, hLR, mul_zero]
  have hcc : c*c = 0 := by rw [show c*c = c*PR*c by rw [hcR], mul_assoc, hRc, mul_zero]
  have hc'c' : c'*c' = 0 := by rw [show c'*c' = c'*PL*c' by rw [hc'L], mul_assoc, hLc', mul_zero]
  have huR : u*PR = 0 := by rw [← huL, mul_assoc, hLR, mul_zero]
  have hLv : PL*v = 0 := by rw [← hRv, ← mul_assoc, hLR, zero_mul]
  have huc' : u*c' = 0 := by rw [← huL, mul_assoc, hLc', mul_zero]
  have hvc' : v*c' = -c' := by rw [← hc'R, ← mul_assoc, hvR, neg_mul]
  have hc'u : c'*u = -c' := by rw [← hc'L, mul_assoc, hLu, mul_neg]
  have huu : u*u = -u := by rw [show u*u = u*PL*u by rw [huL], mul_assoc, hLu, mul_neg, huL]
  have hvv : v*v = -v := by rw [show v*v = v*(PR*v) by rw [hRv], ← mul_assoc, hvR, neg_mul, hRv]
  have huv : u*v = 0 := by rw [show u*v = u*PL*(PR*v) by rw [huL, hRv], mul_assoc, ← mul_assoc PL, hLR, zero_mul, mul_zero]
  have hc'v : c'*v = 0 := by rw [← hRv, ← mul_assoc, hc'R0, zero_mul]
  have g : ∀ {a b d : R}, a * b = d → ∀ x, x * a * b = x * d := fun h x => by rw [mul_assoc, h]
  constructor
  · simp only [mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul, ← mul_assoc, mul_neg, neg_mul,
      hLL, hRR, hLR, hRL, hcL, hcR, hc'R, hc'L, hcc', hc'c, hLu, huL, hvR, hRv, hvu, hRc, hcL0, hLc',
      hc'R0, hcc, hc'c', huR, hLv, huc', hvc', hc'u, huu, hvv, huv, hc'v,
      g hLL, g hRR, g hLR, g hRL, g hcL, g hcR, g hc'R, g hc'L, g hcc', g hc'c, g hLu, g huL, g hvR,
      g hRv, g hvu, g hRc, g hcL0, g hLc', g hc'R0, g hcc, g hc'c', g huR, g hLv, g huc', g hvc',
      g hc'u, g huu, g hvv, g huv, g hc'v, mul_zero, zero_mul, neg_neg, neg_zero]
    abel
  · simp only [mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul, ← mul_assoc, mul_neg, neg_mul,
      hLL, hRR, hLR, hRL, hcL, hcR, hc'R, hc'L, hcc', hc'c, hLu, huL, hvR, hRv, hvu, hRc, hcL0, hLc',
      hc'R0, hcc, hc'c', huR, hLv, huc', hvc', hc'u, huu, hvv, huv, hc'v,
      g hLL, g hRR, g hLR, g hRL, g hcL, g hcR, g hc'R, g hc'L, g hcc', g hc'c, g hLu, g huL, g hvR,
      g hRv, g hvu, g hRc, g hcL0, g hLc', g hc'R0, g hcc, g hc'c', g huR, g hLv, g huc', g hvc',
      g hc'u, g huu, g hvv, g huv, g hc'v, mul_zero, zero_mul, neg_neg, neg_zero]
    abel




lemma finrank_range_prodMap {V W V' W' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    [FiniteDimensional K W] [FiniteDimensional K W']
    (f : V →ₗ[K] W) (g : V' →ₗ[K] W') :
    Module.finrank K (LinearMap.range (f.prodMap g)) =
      Module.finrank K (LinearMap.range f) + Module.finrank K (LinearMap.range g) := by
  have h : LinearMap.range (f.prodMap g) =
      LinearMap.range ((LinearMap.range f).subtype.prodMap (LinearMap.range g).subtype) := by
    rw [LinearMap.range_prodMap, LinearMap.range_prodMap, Submodule.range_subtype,
      Submodule.range_subtype]
  rw [h, LinearMap.finrank_range_of_inj, Module.finrank_prod]
  intro x y hxy
  simp only [LinearMap.prodMap_apply, Prod.mk.injEq] at hxy
  exact Prod.ext (Subtype.ext hxy.1) (Subtype.ext hxy.2)

lemma rank_fromBlocks_diag {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [DecidableEq γ] [DecidableEq δ]
    (A : Matrix α γ K) (B : Matrix β δ K) : (fromBlocks A 0 0 B).rank = A.rank + B.rank := by
  let e1 := LinearEquiv.sumArrowLequivProdArrow α β K K
  let e2 := LinearEquiv.sumArrowLequivProdArrow γ δ K K
  have h : (fromBlocks A 0 0 B).mulVecLin =
      e1.symm.toLinearMap ∘ₗ (A.mulVecLin.prodMap B.mulVecLin) ∘ₗ e2.toLinearMap := by
    apply LinearMap.ext; intro x
    ext (i | i) <;> simp [e1, e2, fromBlocks_mulVec, LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl,
      LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr] <;> rfl
  rw [rank, h, LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
    LinearEquiv.finrank_map_eq, finrank_range_prodMap]
  rfl

lemma rank_idem {m : ℕ} (p : Matrix (Fin m) (Fin m) K) (hp : p * p = p) :
    p.rank + (1 - p).rank = m := by
  have hker : LinearMap.range (1 - p).mulVecLin = LinearMap.ker p.mulVecLin := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      simp only [LinearMap.mem_ker, mulVecLin_apply, mulVec_mulVec, mul_sub, mul_one, hp, sub_self,
        zero_mulVec]
    · intro v hv
      rw [LinearMap.mem_ker, mulVecLin_apply] at hv
      exact ⟨v, by simp [sub_mulVec, hv]⟩
  rw [rank, rank, hker, LinearMap.finrank_range_add_finrank_ker, Module.finrank_fin_fun]

lemma cur {m k : ℕ} (q : Matrix (Fin m) (Fin m) K) (S : Matrix (Fin m) (Fin k) K)
    (T : Matrix (Fin k) (Fin m) K) (hq : q.rank = k) (hu : IsUnit (T * q * S).det) :
    q = q * S * ((T * q * S)⁻¹ * T * q) := by
  have hTqS : (T * q * S).rank = k := by
    rw [rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 hu), Fintype.card_fin]
  have hrS : (q * S).rank = k := by
    apply le_antisymm
    · exact (rank_mul_le_left _ _).trans hq.le
    · calc k = (T * q * S).rank := hTqS.symm
        _ ≤ (q * S).rank := by rw [Matrix.mul_assoc]; exact rank_mul_le_right _ _
  have hle : LinearMap.range (q * S).mulVecLin ≤ LinearMap.range q.mulVecLin := by
    rw [mulVecLin_mul]; exact LinearMap.range_comp_le_range _ _
  have heq : LinearMap.range (q * S).mulVecLin = LinearMap.range q.mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq hle (by
      change (q * S).rank = q.rank; rw [hrS, hq])
  have hall : ∀ j : Fin m, ∃ w : Fin k → K, (q * S) *ᵥ w = fun i => q i j := by
    intro j
    have : (fun i => q i j) ∈ LinearMap.range q.mulVecLin :=
      ⟨Pi.single j 1, by ext i; simp [mulVecLin_apply, mulVec_single_one]⟩
    rw [← heq] at this
    obtain ⟨w, hw⟩ := this
    exact ⟨w, hw⟩
  choose w hw using hall
  set Λ : Matrix (Fin k) (Fin m) K := of fun a j => w j a with hΛ
  have hqΛ : q = q * S * Λ := by
    ext i j
    have := congrFun (hw j) i
    rw [← this]
    simp [mulVec, dotProduct, mul_apply, hΛ]
  have hΛ' : Λ = (T * q * S)⁻¹ * T * q := by
    have h1 : T * q = (T * q * S) * Λ := by
      conv_lhs => rw [hqΛ]
      simp only [Matrix.mul_assoc]
    calc Λ = (T * q * S)⁻¹ * (T * q * S) * Λ := by rw [nonsing_inv_mul _ hu, Matrix.one_mul]
      _ = (T * q * S)⁻¹ * (T * q) := by rw [Matrix.mul_assoc, ← h1]
      _ = (T * q * S)⁻¹ * T * q := (Matrix.mul_assoc _ _ _).symm
  rw [← hΛ']
  exact hqΛ




def Lower {m : ℕ} (E : Matrix (Fin m) (Fin m) K) : Prop := ∀ i j, i < j → E i j = 0

lemma lower_mul {m : ℕ} {E F : Matrix (Fin m) (Fin m) K} (hE : Lower E) (hF : Lower F) :
    Lower (E * F) := by
  intro i j hij
  rw [mul_apply]
  refine Finset.sum_eq_zero fun t _ => ?_
  rcases lt_or_ge i t with h | h
  · rw [hE i t h, zero_mul]
  · rw [hF t j (lt_of_le_of_lt h hij), mul_zero]

lemma strict_entry {m : ℕ} (a : ℕ) (d1 d2 : Fin m → K) (Y : Matrix (Fin m) (Fin m) K)
    (h1 : ∀ i : Fin m, i.val < a → d1 i = 0) (h2 : ∀ j : Fin m, a ≤ j.val → d2 j = 0)
    (i j : Fin m) (hij : i ≤ j) : (diagonal d1 * Y * diagonal d2) i j = 0 := by
  rw [mul_diagonal, diagonal_mul]
  by_cases hi : i.val < a
  · rw [h1 i hi, zero_mul, zero_mul]
  · rw [h2 j (le_trans (not_lt.1 hi) (Fin.le_iff_val_le_val.1 hij)), mul_zero]

lemma lower_one_add {m : ℕ} (Z : Matrix (Fin m) (Fin m) K) (hZ : ∀ i j, i ≤ j → Z i j = 0) :
    Lower (1 + Z) := by
  intro i j hij
  rw [Matrix.add_apply, one_apply_ne hij.ne, hZ i j hij.le, add_zero]

lemma lower_one_sub {m : ℕ} (Z : Matrix (Fin m) (Fin m) K) (hZ : ∀ i j, i ≤ j → Z i j = 0) :
    Lower (1 - Z) := by
  intro i j hij
  rw [Matrix.sub_apply, one_apply_ne hij.ne, hZ i j hij.le, sub_zero]

def NE {m : ℕ} (N : Matrix (Fin m) (Fin m) K) (X Y : ℕ) :
    Matrix {r : Fin m // r.val < X} {c : Fin m // Y ≤ c.val} K :=
  N.submatrix (fun r => r.1) (fun c => c.1)

lemma sum_sub {m : ℕ} {p : Fin m → Prop} [DecidablePred p] (f : Fin m → K)
    (hf : ∀ a, ¬ p a → f a = 0) : ∑ a, f a = ∑ a : {a // p a}, f a.1 := by
  rw [← Finset.sum_subtype (univ.filter p) (by simp) f, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · rfl
  · exact hf a h

lemma ne_le {m : ℕ} (E N F : Matrix (Fin m) (Fin m) K) (hE : Lower E) (hF : Lower F) (X Y : ℕ) :
    (NE (E * N * F) X Y).rank ≤ (NE N X Y).rank := by
  classical
  have hfac : NE (E * N * F) X Y =
      E.submatrix (fun r : {r : Fin m // r.val < X} => r.1) (fun r : {r : Fin m // r.val < X} => r.1) *
        NE N X Y *
        F.submatrix (fun c : {c : Fin m // Y ≤ c.val} => c.1) (fun c : {c : Fin m // Y ≤ c.val} => c.1) := by
    ext r c
    simp only [NE, submatrix_apply, mul_apply]
    rw [sum_sub (p := fun b : Fin m => Y ≤ b.val) (fun b => (∑ a, E r.1 a * N a b) * F b c.1)
      (fun b hb => by
        rw [hF b c.1 (Fin.lt_def.2 (lt_of_lt_of_le (not_le.1 hb) c.2)), mul_zero])]
    refine Finset.sum_congr rfl fun b _ => ?_
    congr 1
    exact sum_sub (p := fun a : Fin m => a.val < X) (fun a => E r.1 a * N a b.1)
      (fun a ha => by
        rw [hE r.1 a (Fin.lt_def.2 (lt_of_lt_of_le r.2 (not_lt.1 ha))), zero_mul])
  rw [hfac]
  exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)

/-- Rank is unchanged by deleting zero rows/columns. -/
lemma rank_eq_of_support {ι κ α β : Type*} [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]
    [DecidableEq ι] [DecidableEq κ] (N : Matrix ι κ K) (f : α → ι) (g : β → κ)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hN : ∀ i j, N i j ≠ 0 → (∃ a, f a = i) ∧ (∃ b, g b = j)) :
    N.rank = (N.submatrix f g).rank := by
  classical
  apply le_antisymm
  · let Sf : Matrix ι α K := of fun i a => if f a = i then 1 else 0
    let Sg : Matrix β κ K := of fun b j => if g b = j then 1 else 0
    have h : N = Sf * N.submatrix f g * Sg := by
      ext i j
      simp only [mul_apply, Sf, Sg, of_apply, submatrix_apply, ite_mul, one_mul, zero_mul,
        mul_ite, mul_one, mul_zero]
      by_cases hij : (∃ a, f a = i) ∧ (∃ b, g b = j)
      · obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := hij
        rw [Finset.sum_eq_single b]
        · rw [if_pos rfl, Finset.sum_eq_single a]
          · rw [if_pos rfl]
          · intro a' _ ha'; rw [if_neg (fun h => ha' (hf h))]
          · simp
        · intro b' _ hb'; rw [if_neg (fun h => hb' (hg h))]
        · simp
      · have h0 : N i j = 0 := by
          by_contra h; exact hij (hN i j h)
        rw [h0]
        refine (Finset.sum_eq_zero fun b _ => ?_).symm
        split_ifs with hb
        · refine Finset.sum_eq_zero fun a _ => ?_
          rw [if_neg]
          intro ha; exact hij ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
        · rfl
    conv_lhs => rw [h]
    exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
  · exact rank_submatrix_le _ _ _




def Sv (m : ℕ) {k : ℕ} (g : Fin k → ℕ) : Matrix (Fin m) (Fin k) K :=
  of fun i a => if i.val = g a then 1 else 0

lemma Sv_t_mul {m k : ℕ} {ν : Type*} (g : Fin k → ℕ) (hg : ∀ a, g a < m) (N : Matrix (Fin m) ν K)
    (a : Fin k) (j : ν) : ((Sv (K := K) m g)ᵀ * N) a j = N ⟨g a, hg a⟩ j := by
  rw [mul_apply, Finset.sum_eq_single ⟨g a, hg a⟩]
  · simp [Sv]
  · intro b _ hb
    simp only [transpose_apply, Sv, of_apply]
    rw [if_neg (fun h => hb (Fin.ext h)), zero_mul]
  · simp

lemma mul_Sv {m k : ℕ} {ν : Type*} [Fintype ν] (g : Fin k → ℕ) (hg : ∀ a, g a < m)
    (N : Matrix ν (Fin m) K) (i : ν) (b : Fin k) :
    (N * (Sv (K := K) m g)) i b = N i ⟨g b, hg b⟩ := by
  rw [mul_apply, Finset.sum_eq_single ⟨g b, hg b⟩]
  · simp [Sv]
  · intro a _ ha
    simp only [Sv, of_apply]
    rw [if_neg (fun h => ha (Fin.ext h)), mul_zero]
  · simp

lemma Sv_mul_t {m k : ℕ} (g : Fin k → ℕ) (hg : Function.Injective g) :
    (Sv (K := K) m g) * (Sv (K := K) m g)ᵀ =
      diagonal fun i : Fin m => if ∃ a, g a = i.val then (1 : K) else 0 := by
  classical
  ext i j
  rw [mul_apply, diagonal_apply]
  simp only [transpose_apply, Sv, of_apply, ite_mul, one_mul, zero_mul]
  by_cases hex : ∃ a, g a = i.val
  · obtain ⟨a, ha⟩ := hex
    rw [Finset.sum_eq_single a]
    · rw [if_pos ha.symm]
      by_cases hij : i = j
      · subst hij; simp [ha]; exact ⟨a, ha⟩
      · rw [if_neg hij, if_neg]; intro h; exact hij (Fin.ext (by omega))
    · intro b _ hb
      rw [if_neg]; intro h; exact hb (hg (by omega))
    · simp
  · rw [if_neg hex]
    simp only [ite_self]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [if_neg]; intro h; exact hex ⟨a, h.symm⟩

lemma rassoc {α β γ : Type*} {δ : Type} [Fintype β] [Fintype γ] {a : Matrix α β K}
    {b : Matrix β γ K} {d : Matrix α γ K} (h : a * b = d) (x : Matrix γ δ K) :
    a * (b * x) = d * x := by rw [← Matrix.mul_assoc, h]


lemma rassoc3 {α β γ ε : Type*} {δ : Type} [Fintype β] [Fintype γ] [Fintype ε] {a : Matrix α β K}
    {b : Matrix β γ K} {c : Matrix γ ε K} {d : Matrix α ε K} (h : a * (b * c) = d)
    (x : Matrix ε δ K) : a * (b * (c * x)) = d * x := by
  rw [← h]; simp only [Matrix.mul_assoc]

end CornerAux

open CornerAux in
theorem solution {m k : ℕ} {K : Type*} [Field K] (hk : 2 * k ≤ m)
    (p : Matrix (Fin m) (Fin m) K) (hp : p * p = p) (hrank : p.rank = m - k)
    (hC : (p.submatrix (fun l : Fin k => (⟨l.val, by omega⟩ : Fin m))
        (fun r : Fin k => (⟨m - k + r.val, by omega⟩ : Fin m))).det ≠ 0)
    (X Y : ℕ) :
    (p.submatrix (fun r : {r : Fin m // r.val < X} => r.1) (fun c : {c : Fin m // Y ≤ c.val} => c.1)).rank =
      ((p.submatrix (fun l : Fin k => (⟨l.val, by omega⟩ : Fin m))
          (fun r : Fin k => (⟨m - k + r.val, by omega⟩ : Fin m))).submatrix
          (fun l : {l : Fin k // l.val < X} => l.1) (fun r : {r : Fin k // Y ≤ m - k + r.val} => r.1)).rank +
      (Finset.univ.filter fun i : Fin m => k ≤ i.val ∧ i.val < m - k ∧ Y ≤ i.val ∧ i.val < X).card := by
  classical
  have hgL : ∀ a : Fin k, (fun a : Fin k => a.val) a < m := fun a => by simp only; omega
  have hgR : ∀ a : Fin k, (fun a : Fin k => m - k + a.val) a < m := fun a => by simp only; omega
  obtain ⟨SL, hSL⟩ : ∃ S : Matrix (Fin m) (Fin k) K, S = Sv m (fun a : Fin k => a.val) := ⟨_, rfl⟩
  obtain ⟨SR, hSR⟩ : ∃ S : Matrix (Fin m) (Fin k) K, S = Sv m (fun a : Fin k => m - k + a.val) :=
    ⟨_, rfl⟩
  have hLtL : SLᵀ * SL = 1 := by
    ext a b; rw [hSL, Sv_t_mul _ hgL, one_apply]; simp [Sv, Fin.ext_iff]
  have hRtR : SRᵀ * SR = 1 := by
    ext a b; rw [hSR, Sv_t_mul _ hgR, one_apply]; simp [Sv, Fin.ext_iff]
  have hLtR : SLᵀ * SR = 0 := by
    ext a b; rw [hSL, hSR, Sv_t_mul _ hgL, Matrix.zero_apply]; simp only [Sv, of_apply]
    rw [if_neg]; omega
  have hRtL : SRᵀ * SL = 0 := by
    ext a b; rw [hSL, hSR, Sv_t_mul _ hgR, Matrix.zero_apply]; simp only [Sv, of_apply]
    rw [if_neg]; omega
  -- diagonal weights
  obtain ⟨dL, hdL⟩ : ∃ d : Fin m → K, d = fun i => if i.val < k then 1 else 0 := ⟨_, rfl⟩
  obtain ⟨dR, hdR⟩ : ∃ d : Fin m → K, d = fun i => if m - k ≤ i.val then 1 else 0 := ⟨_, rfl⟩
  have hPLd : SL * SLᵀ = diagonal dL := by
    rw [hSL, Sv_mul_t _ (fun a b h => Fin.ext h), hdL]
    congr 1; funext i
    congr 1; apply propext
    exact ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun h => ⟨⟨i.val, h⟩, rfl⟩⟩
  have hPRd : SR * SRᵀ = diagonal dR := by
    rw [hSR, Sv_mul_t _ (fun a b h => Fin.ext (by omega)), hdR]
    congr 1; funext i
    congr 1; apply propext
    exact ⟨fun ⟨a, ha⟩ => by omega, fun h => ⟨⟨i.val - (m - k), by omega⟩, by simp only; omega⟩⟩
  -- the corner
  obtain ⟨Cm, hCm⟩ : ∃ C : Matrix (Fin k) (Fin k) K, C = SLᵀ * p * SR := ⟨_, rfl⟩
  have hCmE : Cm = p.submatrix (fun l : Fin k => (⟨l.val, by omega⟩ : Fin m))
        (fun r : Fin k => (⟨m - k + r.val, by omega⟩ : Fin m)) := by
    ext a b; rw [hCm, hSR, mul_Sv _ hgR, hSL, Sv_t_mul _ hgL]; rfl
  have hdet : IsUnit Cm.det := by rw [hCmE]; exact isUnit_iff_ne_zero.2 hC
  have hCi : Cm * Cm⁻¹ = 1 := mul_nonsing_inv _ hdet
  have hiC : Cm⁻¹ * Cm = 1 := nonsing_inv_mul _ hdet
  obtain ⟨q, hq⟩ : ∃ q : Matrix (Fin m) (Fin m) K, q = 1 - p := ⟨_, rfl⟩
  have hpq : p = 1 - q := by rw [hq, sub_sub_cancel]
  have hqq : q * q = q := by
    rw [hq]; simp only [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, hp]; abel
  have hqrank : q.rank = k := by
    have := rank_idem p hp; rw [hrank, ← hq] at this; omega
  have hTqS : -SLᵀ * q * SR = Cm := by
    rw [hq, hCm, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.neg_mul, Matrix.neg_mul,
      Matrix.neg_mul, hLtR, sub_eq_add_neg, neg_neg, neg_zero, zero_add]
  have hcur := cur q SR (-SLᵀ) hqrank (by rw [hTqS]; exact hdet)
  rw [hTqS] at hcur
  have hTqS' : SLᵀ * (q * SR) = -Cm := by
    rw [← hTqS, Matrix.neg_mul, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
  have hqc'q : q * (SR * (Cm⁻¹ * (SLᵀ * q))) = -q := by
    conv_rhs => rw [hcur]
    simp only [Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
  -- algebraic reduction
  obtain ⟨PL, hPL⟩ : ∃ X : Matrix (Fin m) (Fin m) K, X = SL * SLᵀ := ⟨_, rfl⟩
  obtain ⟨PR, hPR⟩ : ∃ X : Matrix (Fin m) (Fin m) K, X = SR * SRᵀ := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ X : Matrix (Fin m) (Fin m) K, X = SL * Cm * SRᵀ := ⟨_, rfl⟩
  obtain ⟨c', hc'⟩ : ∃ X : Matrix (Fin m) (Fin m) K, X = SR * Cm⁻¹ * SLᵀ := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ X : Matrix (Fin m) (Fin m) K, X = q * c' := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ X : Matrix (Fin m) (Fin m) K, X = c' * q := ⟨_, rfl⟩
  have hLL : PL * PL = PL := by
    subst hPL; simp only [Matrix.mul_assoc, rassoc hLtL, Matrix.one_mul, Matrix.mul_one]
  have hRR : PR * PR = PR := by
    subst hPR; simp only [Matrix.mul_assoc, rassoc hRtR, Matrix.one_mul, Matrix.mul_one]
  have hLR : PL * PR = 0 := by
    subst hPL hPR; simp only [Matrix.mul_assoc, rassoc hLtR, Matrix.zero_mul, Matrix.mul_zero]
  have hRL : PR * PL = 0 := by
    subst hPL hPR; simp only [Matrix.mul_assoc, rassoc hRtL, Matrix.zero_mul, Matrix.mul_zero]
  have hcL : PL * c = c := by
    subst hPL hc; simp only [Matrix.mul_assoc, rassoc hLtL, Matrix.one_mul, Matrix.mul_one]
  have hcR : c * PR = c := by
    subst hPR hc; simp only [Matrix.mul_assoc, rassoc hRtR, Matrix.one_mul, Matrix.mul_one, hRtR]
  have hc'R : PR * c' = c' := by
    subst hPR hc'; simp only [Matrix.mul_assoc, rassoc hRtR, Matrix.one_mul, Matrix.mul_one]
  have hc'L : c' * PL = c' := by
    subst hPL hc'; simp only [Matrix.mul_assoc, rassoc hLtL, Matrix.one_mul, Matrix.mul_one, hLtL]
  have hcc' : c * c' = PL := by
    subst hPL hc hc'
    simp only [Matrix.mul_assoc, rassoc hRtR, rassoc hCi, Matrix.one_mul, Matrix.mul_one]
  have hc'c : c' * c = PR := by
    subst hPR hc hc'
    simp only [Matrix.mul_assoc, rassoc hLtL, rassoc hiC, Matrix.one_mul, Matrix.mul_one]
  have hLu : PL * u = -PL := by
    subst hPL hu hc'
    simp only [Matrix.mul_assoc, rassoc3 hTqS', rassoc hCi, Matrix.one_mul, Matrix.mul_one,
      Matrix.neg_mul, Matrix.mul_neg]
  have huL : u * PL = u := by
    subst hPL hu hc'; simp only [Matrix.mul_assoc, rassoc hLtL, Matrix.one_mul, Matrix.mul_one, hLtL]
  have hvR : v * PR = -PR := by
    subst hPR hv hc'
    simp only [Matrix.mul_assoc, rassoc3 hTqS', hTqS', rassoc hiC, hiC, Matrix.one_mul,
      Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg]
  have hRv : PR * v = v := by
    subst hPR hv hc'; simp only [Matrix.mul_assoc, rassoc hRtR, Matrix.one_mul, Matrix.mul_one, hRtR]
  have hvu : v * u = -c' := by
    subst hu hv hc'
    simp only [Matrix.mul_assoc, rassoc hqq, rassoc3 hTqS', rassoc hiC, Matrix.one_mul,
      Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg]
  have hp' : 1 + u * c * v = p := by
    subst hu hv hc hc'
    rw [hpq]
    simp only [Matrix.mul_assoc, rassoc hLtL, rassoc hRtR, rassoc hCi, Matrix.one_mul, hqc'q,
      sub_eq_add_neg]
  obtain ⟨k1, k2⟩ := alg PL PR c c' u v hLL hRR hLR hRL hcL hcR hc'R hc'L hcc' hc'c hLu huL hvR
    hRv hvu
  rw [hp'] at k1 k2
  -- diagonal descriptions
  have hdL1 : ∀ i : Fin m, i.val < k → dL i = 1 := fun i h => by simp only [hdL]; rw [if_pos h]
  have hdL0 : ∀ i : Fin m, k ≤ i.val → dL i = 0 := fun i h => by
    simp only [hdL]; rw [if_neg (by omega)]
  have hdR1 : ∀ i : Fin m, m - k ≤ i.val → dR i = 1 := fun i h => by simp only [hdR]; rw [if_pos h]
  have hdR0 : ∀ i : Fin m, i.val < m - k → dR i = 0 := fun i h => by
    simp only [hdR]; rw [if_neg (by omega)]
  have one_sub_diag : ∀ d : Fin m → K,
      (1 : Matrix (Fin m) (Fin m) K) - diagonal d = diagonal (fun i => 1 - d i) := by
    intro d; ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [diagonal_apply, one_apply, hij]
  have hPLd' : PL = diagonal dL := by rw [hPL, hPLd]
  have hPRd' : PR = diagonal dR := by rw [hPR, hPRd]
  have h1PL : 1 - PL = diagonal (fun i => 1 - dL i) := by rw [hPLd', one_sub_diag]
  have h1PR : 1 - PR = diagonal (fun i => 1 - dR i) := by rw [hPRd', one_sub_diag]
  have hPM : 1 - PL - PR = diagonal (fun i => 1 - dL i - dR i) := by
    rw [h1PL, hPRd', diagonal_sub]
  -- strictly lower pieces
  have hZ1 : ∀ i j, i ≤ j → ((1 - PL) * u) i j = 0 := by
    intro i j hij
    have e : (1 - PL) * u = diagonal (fun i => 1 - dL i) * u * diagonal dL := by
      rw [← h1PL, ← hPLd', Matrix.mul_assoc, huL]
    rw [e]
    exact strict_entry k _ _ _ (fun i hi => by rw [hdL1 i hi, sub_self])
      (fun j hj => hdL0 j hj) i j hij
  have hZ2 : ∀ i j, i ≤ j → (v * (1 - PL - PR)) i j = 0 := by
    intro i j hij
    have e : v * (1 - PL - PR) = diagonal dR * v * diagonal (fun i => 1 - dL i - dR i) := by
      rw [← hPM, ← hPRd', hRv]
    rw [e]
    exact strict_entry (m - k) _ _ _ (fun i hi => hdR0 i hi)
      (fun j hj => by rw [hdL0 j (by omega), hdR1 j hj]; ring) i j hij
  have hZ3 : ∀ i j, i ≤ j → c' i j = 0 := by
    intro i j hij
    have e : c' = diagonal dR * c' * diagonal dL := by
      rw [← hPRd', ← hPLd', hc'R, hc'L]
    rw [e]
    exact strict_entry (m - k) _ _ _ (fun i hi => hdR0 i hi) (fun j hj => hdL0 j (by omega)) i j hij
  have hZ4 : ∀ i j, i ≤ j → (v * (1 - PR)) i j = 0 := by
    intro i j hij
    have e : v * (1 - PR) = diagonal dR * v * diagonal (fun i => 1 - dR i) := by
      rw [← h1PR, ← hPRd', hRv]
    rw [e]
    exact strict_entry (m - k) _ _ _ (fun i hi => hdR0 i hi)
      (fun j hj => by rw [hdR1 j hj, sub_self]) i j hij
  have hZ5 : ∀ i j, i ≤ j → ((1 - PL - PR) * u) i j = 0 := by
    intro i j hij
    have e : (1 - PL - PR) * u = diagonal (fun i => 1 - dL i - dR i) * u * diagonal dL := by
      rw [← hPM, ← hPLd', Matrix.mul_assoc, huL]
    rw [e]
    exact strict_entry k _ _ _ (fun i hi => by rw [hdL1 i hi, hdR0 i (by omega)]; ring)
      (fun j hj => hdL0 j hj) i j hij
  have LA := lower_mul (lower_mul (lower_one_sub _ hZ3) (lower_one_sub _ hZ2)) (lower_one_add _ hZ1)
  have LB := lower_mul (lower_mul (lower_one_add _ hZ4) (lower_one_sub _ hZ3)) (lower_one_sub _ hZ5)
  have LA' := lower_mul (lower_mul (lower_one_sub _ hZ1) (lower_one_add _ hZ2)) (lower_one_add _ hZ3)
  have LB' := lower_mul (lower_mul (lower_one_add _ hZ5) (lower_one_add _ hZ3)) (lower_one_sub _ hZ4)
  have hrk : (NE p X Y).rank = (NE (1 - PL - PR + c) X Y).rank := by
    apply le_antisymm
    · have h := ne_le _ (1 - PL - PR + c) _ LA' LB' X Y
      have e : (1 - (1 - PL) * u) * (1 + v * (1 - PL - PR)) * (1 + c') * (1 - PL - PR + c) *
          ((1 + (1 - PL - PR) * u) * (1 + c') * (1 - v * (1 - PR))) = p := by
        rw [← k2]; simp only [Matrix.mul_assoc]
      rwa [e] at h
    · have h := ne_le _ p _ LA LB X Y
      have e : (1 - c') * (1 - v * (1 - PL - PR)) * (1 + (1 - PL) * u) * p *
          ((1 + v * (1 - PR)) * (1 - c') * (1 - (1 - PL - PR) * u)) = 1 - PL - PR + c := by
        rw [← k1]; simp only [Matrix.mul_assoc]
      rwa [e] at h
  -- entries of the normal form
  have hc_d : c = diagonal dL * p * diagonal dR := by
    rw [hc, hCm, ← hPLd, ← hPRd]; simp only [Matrix.mul_assoc]
  have hD : ∀ i j, (1 - PL - PR + c) i j =
      (if i = j then 1 - dL i - dR i else 0) + dL i * p i j * dR j := by
    intro i j
    rw [hPM, hc_d, Matrix.add_apply, mul_diagonal, diagonal_mul, diagonal_apply]
  show (NE p X Y).rank = _
  rw [hrk]
  let J := {i : Fin m // k ≤ i.val ∧ i.val < m - k ∧ Y ≤ i.val ∧ i.val < X}
  let F : {l : Fin k // l.val < X} ⊕ J → {r : Fin m // r.val < X} :=
    Sum.elim (fun l => ⟨⟨l.1.val, by omega⟩, l.2⟩) (fun j => ⟨j.1, j.2.2.2.2⟩)
  let G : {r : Fin k // Y ≤ m - k + r.val} ⊕ J → {c : Fin m // Y ≤ c.val} :=
    Sum.elim (fun r => ⟨⟨m - k + r.1.val, by omega⟩, r.2⟩) (fun j => ⟨j.1, j.2.2.2.1⟩)
  have hF : Function.Injective F := by
    rintro (a|a) (b|b) h <;> simp only [F, Sum.elim_inl, Sum.elim_inr, Subtype.ext_iff,
      Fin.ext_iff] at h
    · exact congrArg Sum.inl (Subtype.ext (Fin.ext h))
    · exfalso; have := b.2.1; have := a.1.2; omega
    · exfalso; have := a.2.1; have := b.1.2; omega
    · exact congrArg Sum.inr (Subtype.ext (Fin.ext h))
  have hG : Function.Injective G := by
    rintro (a|a) (b|b) h <;> simp only [G, Sum.elim_inl, Sum.elim_inr, Subtype.ext_iff,
      Fin.ext_iff] at h
    · exact congrArg Sum.inl (Subtype.ext (Fin.ext (by omega)))
    · exfalso; have := b.2.2.1; omega
    · exfalso; have := a.2.2.1; omega
    · exact congrArg Sum.inr (Subtype.ext (Fin.ext h))
  have hsupp : ∀ r0 c0, NE (1 - PL - PR + c) X Y r0 c0 ≠ 0 →
      (∃ a, F a = r0) ∧ (∃ b, G b = c0) := by
    intro r0 c0 h
    simp only [NE, submatrix_apply] at h
    rw [hD] at h
    have hr := r0.2
    have hc0 := c0.2
    by_cases hrc : r0.1.val < k ∧ m - k ≤ c0.1.val
    · refine ⟨⟨Sum.inl ⟨⟨r0.1.val, hrc.1⟩, r0.2⟩, rfl⟩,
        ⟨Sum.inl ⟨⟨c0.1.val - (m - k), by omega⟩, by simp only; omega⟩, ?_⟩⟩
      apply Subtype.ext; apply Fin.ext; simp only [G, Sum.elim_inl]; omega
    · have h2 : dL r0.1 * p r0.1 c0.1 * dR c0.1 = 0 := by
        by_cases h3 : r0.1.val < k
        · rw [hdR0 c0.1 (by omega), mul_zero]
        · rw [hdL0 r0.1 (by omega), zero_mul, zero_mul]
      rw [h2, add_zero] at h
      by_cases heq : r0.1 = c0.1
      · rw [if_pos heq] at h
        have hk1 : k ≤ r0.1.val := by
          by_contra hh; apply h; rw [hdL1 _ (by omega), hdR0 _ (by omega)]; ring
        have hk2 : r0.1.val < m - k := by
          by_contra hh; apply h; rw [hdL0 _ (by omega), hdR1 _ (by omega)]; ring
        have hY : Y ≤ r0.1.val := heq ▸ hc0
        refine ⟨⟨Sum.inr ⟨r0.1, hk1, hk2, hY, hr⟩, rfl⟩, ⟨Sum.inr ⟨r0.1, hk1, hk2, hY, hr⟩, ?_⟩⟩
        exact Subtype.ext heq
      · rw [if_neg heq] at h; exact absurd rfl h
  have hsub : (NE (1 - PL - PR + c) X Y).submatrix F G =
      fromBlocks ((p.submatrix (fun l : Fin k => (⟨l.val, by omega⟩ : Fin m))
          (fun r : Fin k => (⟨m - k + r.val, by omega⟩ : Fin m))).submatrix
          (fun l : {l : Fin k // l.val < X} => l.1) (fun r : {r : Fin k // Y ≤ m - k + r.val} => r.1))
        0 0 (1 : Matrix J J K) := by
    ext (a|a) (b|b)
    · simp only [NE, submatrix_apply, F, G, Sum.elim_inl, fromBlocks_apply₁₁]
      rw [hD, if_neg (fun h => by have := congrArg Fin.val h; simp only at this; omega),
        hdL1 _ (by simp only; omega), hdR1 _ (by simp only; omega)]
      ring
    · simp only [NE, submatrix_apply, F, G, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₁₂]
      have := b.2.1
      rw [hD, if_neg (fun h => by have := congrArg Fin.val h; simp only at this; omega),
        hdR0 _ (by omega), Matrix.zero_apply]
      ring
    · simp only [NE, submatrix_apply, F, G, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₂₁]
      have := a.2.1
      rw [hD, if_neg (fun h => by have := congrArg Fin.val h; simp only at this; omega),
        hdL0 _ (by omega), Matrix.zero_apply]
      ring
    · simp only [NE, submatrix_apply, F, G, Sum.elim_inr, fromBlocks_apply₂₂]
      have h1 := a.2.1
      have h2 := a.2.2.1
      rw [hD, hdL0 _ (by omega), hdR0 _ (by omega), one_apply]
      by_cases hab : a = b
      · subst hab; simp
      · rw [if_neg (fun h => hab (Subtype.ext h)), if_neg hab]; ring
  rw [rank_eq_of_support _ F G hF hG hsupp, hsub, rank_fromBlocks_diag, rank_one,
    Fintype.card_subtype]

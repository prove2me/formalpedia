-- Prove2me | solution 3 for KAdaptability.ObjMILP.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T11:35:17.809992+00:00
-- url     : https://prove2.me/submissions/792e0ca2-173b-4737-8e5a-754732240e30

import Mathlib
import Definitions.Def_KAdaptability_ObjMILP_Problem
import Definitions.Def_KAdaptability_ObjMILP_POK
import Definitions.Def_KAdaptability_ObjMILP_MILP5
import Theorems.Thm_LP_farkas

-- carved verbatim out of submission 68409d51-7f93-472d-85a5-9b7ccebaa982, lines 844-882

section
open Matrix
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def LP.Feas (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ) : Set E :=
  {x | (∀ i, a i x ≤ b i) ∧ ∀ j, e j x = d j}

def LP.DualFeas (a : ι → Module.Dual ℝ E) (e : κ → Module.Dual ℝ E) (c : Module.Dual ℝ E) :
    Set ((ι → ℝ) × (κ → ℝ)) :=
  {yz | 0 ≤ yz.1 ∧ ∑ i, yz.1 i • a i + ∑ j, yz.2 j • e j = c}

theorem LP.weak_duality
    (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E) {x : E} (hx : x ∈ LP.Feas a b e d)
    {yz : (ι → ℝ) × (κ → ℝ)} (hyz : yz ∈ LP.DualFeas a e c) :
    c x ≤ yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d := by
  obtain ⟨hax, hex⟩ := hx
  obtain ⟨hy, hsum⟩ := hyz
  have h := congrArg (fun φ : Module.Dual ℝ E => φ x) hsum
  simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    hex] at h
  have hle : ∑ i, yz.1 i * a i x ≤ ∑ i, yz.1 i * b i :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hax i) (hy i)
  simp only [dotProduct]
  linarith

lemma aux1_alt (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E) (hP : (LP.Feas a b e d).Nonempty) (t : ℝ)
    (h : ∀ x ∈ LP.Feas a b e d, c x < t) :
    ∃ yz ∈ LP.DualFeas a e c, yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d < t := by
  classical
  let a' : Option ι → Module.Dual ℝ E := fun o => o.elim (-c) a
  let b' : Option ι → ℝ := fun o => o.elim (-t) b
  have hinf : ¬ ∃ x : E, (∀ i, a' i x ≤ b' i) ∧ ∀ j, e j x = d j := by
    rintro ⟨x, hx1, hx2⟩
    have h1 := h x ⟨fun i => hx1 (some i), hx2⟩
    have h2 := hx1 none
    simp only [a', b', Option.elim, LinearMap.neg_apply] at h2
    linarith
  obtain ⟨y', z, hy', hsum, hneg⟩ := (LP.farkas a' b' e d).1 hinf
  rw [Fintype.sum_option] at hsum
  simp only [dotProduct, Fintype.sum_option] at hneg
  simp only [a', b', Option.elim, smul_neg] at hsum hneg
  have hy0 : 0 ≤ y' none := hy' none
  rcases hy0.eq_or_lt with h0 | h0
  · exfalso
    obtain ⟨x0, hx0⟩ := hP
    refine (LP.farkas a b e d).2 ⟨fun i => y' (some i), z, fun i => hy' (some i), ?_, ?_⟩
      ⟨x0, hx0⟩
    · rw [← h0] at hsum; simpa using hsum
    · simp only [dotProduct]; rw [← h0] at hneg; simpa using hneg
  · refine ⟨(fun i => y' (some i) / y' none, fun j => z j / y' none),
      ⟨fun i => div_nonneg (hy' _) h0.le, ?_⟩, ?_⟩
    · have hAB : ∑ i, y' (some i) • a i + ∑ j, z j • e j = y' none • c := by
        rw [← sub_eq_zero, ← hsum]; abel
      show ∑ i, (y' (some i) / y' none) • a i + ∑ j, (z j / y' none) • e j = c
      have hr : ∀ (r : ℝ) (φ : Module.Dual ℝ E), (r / y' none) • φ = (y' none)⁻¹ • (r • φ) :=
        fun r φ => by rw [smul_smul, div_eq_inv_mul]
      simp only [hr]
      rw [← Finset.smul_sum, ← Finset.smul_sum, ← smul_add, hAB, smul_smul,
        inv_mul_cancel₀ h0.ne', one_smul]
    · simp only [dotProduct]
      have : ∑ i, y' (some i) / y' none * b i + ∑ j, z j / y' none * d j =
          (∑ i, y' (some i) * b i + ∑ j, z j * d j) / y' none := by
        rw [add_div, Finset.sum_div, Finset.sum_div]
        congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring
      rw [this, div_lt_iff₀ h0]
      linarith

lemma aux1_attain (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E) (hP : (LP.Feas a b e d).Nonempty)
    (hb : BddAbove (c '' LP.Feas a b e d)) :
    ∃ x ∈ LP.Feas a b e d, ∀ x' ∈ LP.Feas a b e d, c x' ≤ c x := by
  by_contra hno
  push Not at hno
  have hlt : ∀ x ∈ LP.Feas a b e d, c x < sSup (c '' LP.Feas a b e d) := fun x hx => by
    obtain ⟨x', hx', hlt⟩ := hno x hx
    exact lt_of_lt_of_le hlt (le_csSup hb ⟨x', hx', rfl⟩)
  obtain ⟨yz, hyz, hobj⟩ := aux1_alt a b e d c hP _ hlt
  have : sSup (c '' LP.Feas a b e d) ≤ yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d :=
    csSup_le (hP.image c) (by rintro _ ⟨x, hx, rfl⟩; exact LP.weak_duality a b e d c hx hyz)
  linarith

def aux1_T (a : ι → Module.Dual ℝ E) (e : κ → Module.Dual ℝ E) :
    (ι → ℝ) × (κ → ℝ) →ₗ[ℝ] Module.Dual ℝ E where
  toFun yz := ∑ i, yz.1 i • a i + ∑ j, yz.2 j • e j
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' t p := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_smul,
      ← Finset.smul_sum, smul_add, RingHom.id_apply]

def aux1_obj (b : ι → ℝ) (d : κ → ℝ) : Module.Dual ℝ ((ι → ℝ) × (κ → ℝ)) where
  toFun yz := yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, add_dotProduct]; ring
  map_smul' t p := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, smul_eq_mul, RingHom.id_apply]; ring

lemma aux1_dualFeas_eq (a : ι → Module.Dual ℝ E) (e : κ → Module.Dual ℝ E) (c : Module.Dual ℝ E) :
    LP.DualFeas a e c =
      LP.Feas (fun i => -(LinearMap.proj i ∘ₗ LinearMap.fst ℝ (ι → ℝ) (κ → ℝ))) 0
        (fun k => Module.Dual.eval ℝ E (Module.finBasis ℝ E k) ∘ₗ aux1_T a e)
        (fun k => c (Module.finBasis ℝ E k)) := by
  ext yz
  simp only [LP.DualFeas, LP.Feas, Set.mem_setOf_eq, LinearMap.neg_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.coe_fst, LinearMap.coe_proj, Function.eval, Pi.zero_apply,
    neg_nonpos, Module.Dual.eval_apply]
  constructor
  · rintro ⟨hy, hsum⟩
    exact ⟨fun i => hy i, fun k => by rw [← hsum]; rfl⟩
  · rintro ⟨hy, hk⟩
    refine ⟨fun i => hy i, ?_⟩
    have : aux1_T a e yz = c := (Module.finBasis ℝ E).ext fun k => hk k
    exact this

lemma aux1_dual_attain (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E)
    (d : κ → ℝ) (c : Module.Dual ℝ E)
    (hP : (LP.Feas a b e d).Nonempty) (hD : (LP.DualFeas a e c).Nonempty) :
    ∃ yz ∈ LP.DualFeas a e c, ∀ yz' ∈ LP.DualFeas a e c,
      yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d ≤ yz'.1 ⬝ᵥ b + yz'.2 ⬝ᵥ d := by
  obtain ⟨x0, hx0⟩ := hP
  rw [aux1_dualFeas_eq] at hD ⊢
  obtain ⟨yz, hyz, hmax⟩ := aux1_attain _ _ _ _ (-aux1_obj b d) hD (by
    refine ⟨-c x0, ?_⟩
    rintro _ ⟨yz', hyz', rfl⟩
    rw [← aux1_dualFeas_eq] at hyz'
    have := LP.weak_duality a b e d c hx0 hyz'
    simp only [LinearMap.neg_apply, neg_le_neg_iff]
    exact this)
  refine ⟨yz, hyz, fun yz' hyz' => ?_⟩
  have := hmax yz' hyz'
  simp only [LinearMap.neg_apply, neg_le_neg_iff] at this
  exact this

theorem LP.strong_duality
    (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E)
    (hP : (LP.Feas a b e d).Nonempty) (hD : (LP.DualFeas a e c).Nonempty) :
    ∃ v : ℝ, IsGreatest (c '' LP.Feas a b e d) v ∧
      IsLeast ((fun yz => yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d) '' LP.DualFeas a e c) v := by
  obtain ⟨yz, hyz, hmin⟩ := aux1_dual_attain a b e d c hP hD
  obtain ⟨x, hx, hxw⟩ : ∃ x ∈ LP.Feas a b e d, yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d ≤ c x := by
    by_contra hcon
    push Not at hcon
    obtain ⟨yz', hyz', hlt⟩ := aux1_alt a b e d c hP _ hcon
    linarith [hmin yz' hyz']
  refine ⟨yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d,
    ⟨⟨x, hx, le_antisymm (LP.weak_duality a b e d c hx hyz) hxw⟩, ?_⟩,
    ⟨⟨yz, hyz, rfl⟩, ?_⟩⟩
  · rintro _ ⟨x', hx', rfl⟩; exact LP.weak_duality a b e d c hx' hyz
  · rintro _ ⟨yz', hyz', rfl⟩; exact hmin yz' hyz'

theorem LP.dualFeas_nonempty_of_bddAbove
    (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E)
    (hP : (LP.Feas a b e d).Nonempty)
    (hb : BddAbove (c '' LP.Feas a b e d)) : (LP.DualFeas a e c).Nonempty := by
  obtain ⟨M, hM⟩ := hb
  obtain ⟨yz, hyz, -⟩ := aux1_alt a b e d c hP (M + 1) fun x hx => by
    have := hM ⟨x, hx, rfl⟩
    linarith
  exact ⟨yz, hyz⟩

def aux1_dotL {n : Type*} [Fintype n] (u : n → ℝ) : Module.Dual ℝ (n → ℝ) where
  toFun v := u ⬝ᵥ v
  map_add' v w := dotProduct_add u v w
  map_smul' t v := by simp [dotProduct_smul]

lemma aux1_dotL_apply {n : Type*} [Fintype n] (u v : n → ℝ) : aux1_dotL u v = u ⬝ᵥ v := rfl

lemma aux1_dotL_inj {n : Type*} [Fintype n] {u w : n → ℝ} (h : aux1_dotL u = aux1_dotL w) :
    u = w := by
  classical
  funext j
  have := congrArg (fun φ : Module.Dual ℝ (n → ℝ) => φ (Pi.single j 1)) h
  simpa [aux1_dotL_apply, dotProduct_single] using this

lemma aux1_sum_dotL {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) (y : m → ℝ) :
    ∑ i, y i • aux1_dotL (A i) = aux1_dotL (Aᵀ *ᵥ y) := by
  ext v
  rw [LinearMap.sum_apply, aux1_dotL_apply, mulVec_transpose, ← dotProduct_mulVec]
  simp only [LinearMap.smul_apply, smul_eq_mul, aux1_dotL_apply, dotProduct]
  rfl

lemma aux1_matFeas {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) (b : m → ℝ)
    (x : n → ℝ) :
    x ∈ LP.Feas (fun i => aux1_dotL (A i)) b (fun j : Empty => j.elim) (fun j => j.elim) ↔
      A *ᵥ x ≤ b :=
  ⟨fun h i => h.1 i, fun h => ⟨fun i => h i, fun j => j.elim⟩⟩

lemma aux1_matDual {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) (c : n → ℝ)
    (yz : (m → ℝ) × (Empty → ℝ)) :
    yz ∈ LP.DualFeas (fun i => aux1_dotL (A i)) (fun j : Empty => j.elim) (aux1_dotL c) ↔
      0 ≤ yz.1 ∧ Aᵀ *ᵥ yz.1 = c := by
  simp only [LP.DualFeas, Set.mem_setOf_eq, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    aux1_sum_dotL]
  exact and_congr Iff.rfl ⟨aux1_dotL_inj, fun h => by rw [h]⟩

theorem LP.strong_duality_matrix {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ)
    (hP : ∃ x, A *ᵥ x ≤ b) (hD : ∃ y, 0 ≤ y ∧ Aᵀ *ᵥ y = c) :
    ∃ x y, A *ᵥ x ≤ b ∧ 0 ≤ y ∧ Aᵀ *ᵥ y = c ∧ c ⬝ᵥ x = b ⬝ᵥ y ∧
      (∀ x', A *ᵥ x' ≤ b → c ⬝ᵥ x' ≤ c ⬝ᵥ x) := by
  obtain ⟨x0, hx0⟩ := hP
  obtain ⟨y0, hy0, hy0c⟩ := hD
  obtain ⟨v, ⟨⟨x, hx, hxv⟩, hub⟩, ⟨⟨yz, hyz, hyzv⟩, -⟩⟩ :=
    LP.strong_duality (fun i => aux1_dotL (A i)) b (fun j : Empty => j.elim) (fun j => j.elim)
      (aux1_dotL c) ⟨x0, (aux1_matFeas A b x0).2 hx0⟩
      ⟨(y0, fun j => j.elim), (aux1_matDual A c _).2 ⟨hy0, hy0c⟩⟩
  obtain ⟨hy, hyc⟩ := (aux1_matDual A c yz).1 hyz
  refine ⟨x, yz.1, (aux1_matFeas A b x).1 hx, hy, hyc, ?_, fun x' hx' => ?_⟩
  · rw [aux1_dotL_apply] at hxv
    have h0 : yz.2 ⬝ᵥ (fun j : Empty => j.elim) = 0 := by simp [dotProduct]
    simp only [h0, add_zero] at hyzv
    rw [hxv, ← hyzv, dotProduct_comm]
  · have := hub ⟨x', (aux1_matFeas A b x').2 hx', rfl⟩
    rw [← hxv] at this
    exact this

theorem LP.exists_dual_of_isBounded {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ) (hne : {x | A *ᵥ x ≤ b}.Nonempty)
    (hbd : Bornology.IsBounded {x | A *ᵥ x ≤ b}) (c : n → ℝ) :
    ∃ y, 0 ≤ y ∧ Aᵀ *ᵥ y = c := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hbd
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨yz, hyz⟩ := LP.dualFeas_nonempty_of_bddAbove (fun i => aux1_dotL (A i)) b
    (fun j : Empty => j.elim) (fun j => j.elim) (aux1_dotL c)
    ⟨x0, (aux1_matFeas A b x0).2 hx0⟩ (by
      refine ⟨∑ i, |c i| * R, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      have hxR := hR x ((aux1_matFeas A b x).1 hx)
      rw [aux1_dotL_apply, dotProduct]
      refine Finset.sum_le_sum fun i _ => ?_
      calc c i * x i ≤ |c i * x i| := le_abs_self _
        _ = |c i| * |x i| := abs_mul _ _
        _ ≤ |c i| * R := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          have := norm_le_pi_norm x i
          rw [Real.norm_eq_abs] at this
          linarith)
  exact ⟨yz.1, (aux1_matDual A c yz).1 hyz⟩

end

section
open Matrix
open KAdaptability.ObjMILP
variable {N M L nQ R : ℕ}

lemma iInf_coe_eq {K : ℕ} (r : Fin K → ℝ) (k0 : Fin K) (hk0 : ∀ k, r k0 ≤ r k) :
    (⨅ k, ((r k : ℝ) : EReal)) = ((r k0 : ℝ) : EReal) :=
  le_antisymm (iInf_le _ k0) (le_iInf fun k => EReal.coe_le_coe_iff.mpr (hk0 k))

lemma mcCormick_eq {M : ℕ} (y z : Fin M → ℝ) (b : ℝ) (hy : ∀ i, y i = 0 ∨ y i = 1)
    (hz0 : 0 ≤ z) (hzy : z ≤ y) (hzb : z ≤ b • (1 : Fin M → ℝ))
    (hzl : (b - 1) • (1 : Fin M → ℝ) + y ≤ z) : z = b • y := by
  funext i
  have h0 := hz0 i; have h1 := hzy i; have h2 := hzb i; have h3 := hzl i
  simp only [Pi.zero_apply, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul,
    mul_one] at h0 h1 h2 h3 ⊢
  rcases hy i with h | h <;> rw [h] at h1 h3 ⊢ <;> linarith

lemma beta_le_one {K : ℕ} (β : Fin K → ℝ) (hβ : 0 ≤ β) (hs : (1 : Fin K → ℝ) ⬝ᵥ β = 1)
    (k : Fin K) : β k ≤ 1 := by
  have hs' : ∑ j, β j = 1 := by simpa [dotProduct] using hs
  rw [← hs']
  exact Finset.single_le_sum (fun j _ => hβ j) (Finset.mem_univ k)

lemma objPOK_le (P : Problem N M L nQ R) (K : ℕ) (x : Fin N → ℝ) (ys zs : Fin K → Fin M → ℝ)
    (α : Fin R → ℝ) (β : Fin K → ℝ) (hF : P.MILPFeasible K x ys zs α β) :
    P.objPOK K x ys ≤ ((P.b ⬝ᵥ α : ℝ) : EReal) := by
  obtain ⟨_, hY, hz0, hα, hβ, hA, hs, hk⟩ := hF
  have hzs : ∀ k, zs k = β k • ys k := fun k =>
    mcCormick_eq (ys k) (zs k) (β k) (P.Y_binary _ (hY k)) (hz0 k) (hk k).2.1 (hk k).2.2.1
      (hk k).2.2.2
  have hK : Nonempty (Fin K) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    simp [dotProduct] at hs
  unfold Problem.objPOK
  refine iSup₂_le fun ξ hξ => ?_
  obtain ⟨k0, hk0⟩ := Finite.exists_min (fun k => ξ ⬝ᵥ (P.Q *ᵥ ys k))
  rw [iInf_coe_eq _ k0 hk0, ← EReal.coe_add, EReal.coe_le_coe_iff]
  -- weighted average ≥ minimum
  have hs' : ∑ j, β j = 1 := by simpa [dotProduct] using hs
  have havg : ξ ⬝ᵥ (P.Q *ᵥ ys k0) ≤ ∑ k, β k * (ξ ⬝ᵥ (P.Q *ᵥ ys k)) := by
    calc ξ ⬝ᵥ (P.Q *ᵥ ys k0) = ∑ k, β k * (ξ ⬝ᵥ (P.Q *ᵥ ys k0)) := by
          rw [← Finset.sum_mul, hs', one_mul]
      _ ≤ _ := Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hk0 k) (hβ k)
  have hid : ξ ⬝ᵥ (P.C *ᵥ x) + ∑ k, β k * (ξ ⬝ᵥ (P.Q *ᵥ ys k)) = (P.A *ᵥ ξ) ⬝ᵥ α := by
    have e : (P.A *ᵥ ξ) ⬝ᵥ α = ξ ⬝ᵥ (P.Aᵀ *ᵥ α) := by rw [dotProduct_mulVec, vecMul_transpose]
    rw [e, hA, dotProduct_add, dotProduct_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hzs k, mulVec_smul, dotProduct_smul, smul_eq_mul]
  have hAb : (P.A *ᵥ ξ) ⬝ᵥ α ≤ P.b ⬝ᵥ α := dotProduct_le_dotProduct_of_nonneg_right hξ hα
  linarith

noncomputable def bigA (P : Problem N M L nQ R) (K : ℕ) (ys : Fin K → Fin M → ℝ) :
    Matrix (Fin R ⊕ Fin K) (Fin nQ ⊕ Unit) ℝ :=
  Matrix.fromBlocks P.A 0 (Matrix.of fun k j => -(P.Q *ᵥ ys k) j) (Matrix.of fun _ _ => 1)

lemma exists_attain (P : Problem N M L nQ R) (K : ℕ) (hK : 0 < K) (x : Fin N → ℝ)
    (ys : Fin K → Fin M → ℝ) (hF : P.FeasibleK K x ys) :
    ∃ (zs : Fin K → Fin M → ℝ) (α : Fin R → ℝ) (β : Fin K → ℝ),
      P.MILPFeasible K x ys zs α β ∧ ((P.b ⬝ᵥ α : ℝ) : EReal) = P.objPOK K x ys := by
  have : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  set bb : Fin R ⊕ Fin K → ℝ := Sum.elim P.b 0 with hbb
  set cc : Fin nQ ⊕ Unit → ℝ := Sum.elim (P.C *ᵥ x) (fun _ => 1) with hcc
  -- primal feasibility
  have hP : ∃ v, bigA P K ys *ᵥ v ≤ bb := by
    obtain ⟨ξ0, hξ0⟩ := P.Xi_nonempty
    obtain ⟨k0, hk0⟩ := Finite.exists_min (fun k => ξ0 ⬝ᵥ (P.Q *ᵥ ys k))
    refine ⟨Sum.elim ξ0 (fun _ => ξ0 ⬝ᵥ (P.Q *ᵥ ys k0)), ?_⟩
    intro i
    rcases i with r | k
    · simpa [bigA, fromBlocks_mulVec, hbb] using hξ0 r
    · have := hk0 k
      simp only [bigA, fromBlocks_mulVec, hbb, Sum.elim_inr, Pi.add_apply, Pi.zero_apply]
      simp only [mulVec, dotProduct, of_apply, Function.comp_apply, Sum.elim_inl, Sum.elim_inr,
        Finset.univ_unique, Finset.sum_singleton, one_mul, neg_mul, Finset.sum_neg_distrib]
      simp only [dotProduct, mulVec] at this
      have e : ∑ x, (∑ x_1, P.Q x x_1 * ys k x_1) * ξ0 x = ∑ i, ξ0 i * ∑ j, P.Q i j * ys k j :=
        Finset.sum_congr rfl fun _ _ => mul_comm _ _
      linarith
  -- dual feasibility
  have hD : ∃ w, 0 ≤ w ∧ (bigA P K ys)ᵀ *ᵥ w = cc := by
    let k0 : Fin K := ⟨0, hK⟩
    obtain ⟨α0, hα0, hA0⟩ := LP.exists_dual_of_isBounded P.A P.b P.Xi_nonempty
      P.Xi_bounded (P.C *ᵥ x + P.Q *ᵥ ys k0)
    refine ⟨Sum.elim α0 (fun k => if k = k0 then 1 else 0), ?_, ?_⟩
    · intro i
      rcases i with r | k
      · exact hα0 r
      · simp only [Sum.elim_inr, Pi.zero_apply]; split_ifs <;> norm_num
    · funext j
      rcases j with j | u
      · have := congrFun hA0 j
        simp only [bigA, fromBlocks_transpose, fromBlocks_mulVec, hcc, Sum.elim_inl,
          Pi.add_apply, Function.comp_def] at this ⊢
        rw [this]
        simp [mulVec, dotProduct, transpose_apply, of_apply]
      · simp [bigA, hcc, mulVec, dotProduct]
  obtain ⟨v, w, hv, hw0, hwA, hval, -⟩ := LP.strong_duality_matrix _ bb cc hP hD
  set ξ : Fin nQ → ℝ := v ∘ Sum.inl with hξdef
  set t : ℝ := v (Sum.inr ()) with htdef
  set α : Fin R → ℝ := w ∘ Sum.inl with hαdef
  set β : Fin K → ℝ := w ∘ Sum.inr with hβdef
  -- extract primal facts
  have hξ : ξ ∈ P.Xi := by
    intro r
    have := hv (Sum.inl r)
    simpa [bigA, fromBlocks_mulVec, hbb, Function.comp_def, hξdef] using this
  have ht : ∀ k, t ≤ ξ ⬝ᵥ (P.Q *ᵥ ys k) := by
    intro k
    have := hv (Sum.inr k)
    simp only [bigA, fromBlocks_mulVec, hbb, Sum.elim_inr, Pi.add_apply, Pi.zero_apply] at this
    simp only [mulVec, dotProduct, of_apply, Function.comp_apply, Finset.univ_unique,
      Finset.sum_singleton, one_mul, neg_mul, Finset.sum_neg_distrib] at this
    have e : ∑ x, (∑ x_1, P.Q x x_1 * ys k x_1) * v (Sum.inl x) =
        ξ ⬝ᵥ (P.Q *ᵥ ys k) := by
      simp only [dotProduct, mulVec, hξdef, Function.comp_apply]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    have : t = v (Sum.inr default) := rfl
    linarith
  -- extract dual facts
  have hα : 0 ≤ α := fun r => hw0 (Sum.inl r)
  have hβ : 0 ≤ β := fun k => hw0 (Sum.inr k)
  have hsum : (1 : Fin K → ℝ) ⬝ᵥ β = 1 := by
    have := congrFun hwA (Sum.inr ())
    simpa [bigA, fromBlocks_transpose, fromBlocks_mulVec, hcc, mulVec, dotProduct,
      Function.comp_def, hβdef] using this
  have hAα : P.Aᵀ *ᵥ α = P.C *ᵥ x + ∑ k, P.Q *ᵥ (β k • ys k) := by
    funext j
    have := congrFun hwA (Sum.inl j)
    simp only [bigA, fromBlocks_transpose, fromBlocks_mulVec, hcc, Sum.elim_inl,
      Pi.add_apply] at this
    have e : ((of fun k j => -(P.Q *ᵥ ys k) j : Matrix (Fin K) (Fin nQ) ℝ)ᵀ *ᵥ
        (w ∘ Sum.inr)) j = -∑ k, β k * (P.Q *ᵥ ys k) j := by
      simp only [mulVec, dotProduct, transpose_apply, of_apply, hβdef, neg_mul,
        Finset.sum_neg_distrib]
      exact congrArg _ (Finset.sum_congr rfl fun _ _ => mul_comm _ _)
    simp only [mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    rw [e] at this
    have hα' : (P.Aᵀ *ᵥ α) j = (P.Aᵀ *ᵥ (w ∘ Sum.inl)) j := rfl
    linarith
  have hvalue : P.b ⬝ᵥ α = ξ ⬝ᵥ (P.C *ᵥ x) + t := by
    have e1 : cc ⬝ᵥ v = (P.C *ᵥ x) ⬝ᵥ ξ + t := by
      simp [hcc, dotProduct, Fintype.sum_sum_type, hξdef, htdef]
    have e2 : bb ⬝ᵥ w = P.b ⬝ᵥ α := by
      simp [hbb, dotProduct, Fintype.sum_sum_type, hαdef]
    rw [← e2, ← hval, e1, dotProduct_comm]
  have hFeas : P.MILPFeasible K x ys (fun k => β k • ys k) α β := by
    obtain ⟨hX, hk⟩ := hF
    refine ⟨hX, fun k => (hk k).1, ?_, hα, hβ, hAα, hsum, fun k => ⟨(hk k).2, ?_, ?_, ?_⟩⟩
    · intro k i
      have hb0 : 0 ≤ β k := hβ k
      simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
      rcases P.Y_binary _ (hk k).1 i with h | h <;> simp [h, hb0]
    all_goals
      intro i
      have hb1 := beta_le_one β hβ hsum k
      have hb0 : 0 ≤ β k := hβ k
      simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
      rcases P.Y_binary _ (hk k).1 i with h | h <;> rw [h] <;> linarith
  refine ⟨fun k => β k • ys k, α, β, hFeas, le_antisymm ?_ (objPOK_le P K x ys _ α β hFeas)⟩
  unfold Problem.objPOK
  refine le_trans ?_ (le_iSup₂ (f := fun ξ (_ : ξ ∈ P.Xi) =>
    (((ξ ⬝ᵥ (P.C *ᵥ x) : ℝ) : EReal) + ⨅ k, ((ξ ⬝ᵥ (P.Q *ᵥ ys k) : ℝ) : EReal))) ξ hξ)
  rw [hvalue, EReal.coe_add]
  exact add_le_add le_rfl (le_iInf fun k => EReal.coe_le_coe_iff.mpr (ht k))

end

section
open Matrix

open KAdaptability.ObjMILP in
theorem solution {N M L nQ R : ℕ} (P : Problem N M L nQ R) (K : ℕ) (hK : 0 < K) :
    (∀ (x : Fin N → ℝ) (ys : Fin K → Fin M → ℝ),
      P.FeasibleK K x ys ↔
        ∃ (zs : Fin K → Fin M → ℝ) (α : Fin R → ℝ) (β : Fin K → ℝ),
          P.MILPFeasible K x ys zs α β) ∧
    (∀ (x : Fin N → ℝ) (ys : Fin K → Fin M → ℝ), P.FeasibleK K x ys →
      P.objPOK K x ys = P.milpValueAt K x ys ∧
        ∃ (zs : Fin K → Fin M → ℝ) (α : Fin R → ℝ) (β : Fin K → ℝ),
          P.MILPFeasible K x ys zs α β ∧ ((P.b ⬝ᵥ α : ℝ) : EReal) = P.objPOK K x ys) ∧
    P.optPOK K = P.optMILP K := by
  have hfeas : ∀ x ys zs α β, P.MILPFeasible K x ys zs α β → P.FeasibleK K x ys :=
    fun x ys zs α β h => ⟨h.1, fun k => ⟨h.2.1 k, (h.2.2.2.2.2.2.2 k).1⟩⟩
  refine ⟨fun x ys => ⟨fun h => ?_, fun ⟨zs, α, β, h⟩ => hfeas x ys zs α β h⟩,
    fun x ys h => ⟨?_, exists_attain P K hK x ys h⟩, ?_⟩
  · obtain ⟨zs, α, β, h', -⟩ := exists_attain P K hK x ys h
    exact ⟨zs, α, β, h'⟩
  · obtain ⟨zs, α, β, h', he⟩ := exists_attain P K hK x ys h
    refine le_antisymm ?_ ?_
    · unfold Problem.milpValueAt
      exact le_iInf fun zs => le_iInf fun α => le_iInf fun β => le_iInf fun hF =>
        objPOK_le P K x ys zs α β hF
    · rw [← he]
      unfold Problem.milpValueAt
      exact iInf_le_of_le zs <| iInf_le_of_le α <| iInf_le_of_le β <| iInf_le _ h'
  · refine le_antisymm ?_ ?_
    · unfold Problem.optMILP Problem.optPOK
      refine le_iInf fun x => le_iInf fun ys => le_iInf fun zs => le_iInf fun α =>
        le_iInf fun β => le_iInf fun hF => ?_
      exact iInf_le_of_le x <| iInf_le_of_le ys <| iInf_le_of_le (hfeas x ys zs α β hF) <|
        objPOK_le P K x ys zs α β hF
    · unfold Problem.optMILP Problem.optPOK
      refine le_iInf fun x => le_iInf fun ys => le_iInf fun hF => ?_
      obtain ⟨zs, α, β, h', he⟩ := exists_attain P K hK x ys hF
      rw [← he]
      exact iInf_le_of_le x <| iInf_le_of_le ys <| iInf_le_of_le zs <| iInf_le_of_le α <|
        iInf_le_of_le β <| iInf_le _ h'

end

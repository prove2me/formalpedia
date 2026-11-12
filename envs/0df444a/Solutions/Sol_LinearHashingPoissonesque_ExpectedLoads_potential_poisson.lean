-- Prove2me | solution 1 for LinearHashingPoissonesque.ExpectedLoads.potential_poisson
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T22:14:52.294211+00:00
-- url     : https://prove2.me/submissions/a562ad3b-13c8-4ecc-a95b-8b34c948e0bc

import Mathlib
import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_KernelPotential
import Theorems.Thm_LinearHashingPoissonesque_ExpectedLoads_conditional_squaring
import Definitions.Def_LinMaxLoad_avgLin
import Definitions.Def_LinMaxLoad_condAvgLin
import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_LogPotential
import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_ExtremeLoads
import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_LoadVector
import Theorems.Thm_LinearHashingPoissonesque_ExpectedLoads_remove_surjectivity
import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_BinLoad

section
set_option autoImplicit false

namespace LinearHashingPoissonesque.Dev.PotIter
open LinearHashingPoissonesque.ExpectedLoads

noncomputable def Ind (U i : ℕ) : Finset (Fin i → BinaryVector U) := by
  classical exact Finset.univ.filter (fun v => LinearIndependent (ZMod 2) v)

lemma mem_Ind {U i : ℕ} (v : Fin i → BinaryVector U) :
    v ∈ Ind U i ↔ LinearIndependent (ZMod 2) v := by
  classical simp [Ind]

lemma card_next {U i : ℕ} {v : Fin i → BinaryVector U} (hv : LinearIndependent (ZMod 2) v) :
    ((nextVectors v).card : ℝ) = 2 ^ U - 2 ^ i := by
  classical
  have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (BinaryVector U)))
    (fun w => w ∈ tupleSpan v)
  have h2 : (Finset.univ.filter (fun w : BinaryVector U => w ∈ tupleSpan v)).card = 2 ^ i := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := ZMod 2)]
    rw [tupleSpan, finrank_span_eq_card hv]
    simp
  have h3 : (Finset.univ : Finset (BinaryVector U)).card = 2 ^ U := by
    simp
  have h4 : (nextVectors v).card = (Finset.univ.filter (fun w : BinaryVector U => ¬ w ∈ tupleSpan v)).card := by
    unfold nextVectors; congr
  rw [h2, h3] at h1
  have : (nextVectors v).card + 2 ^ i = 2 ^ U := by omega
  have h5 : ((nextVectors v).card : ℝ) + 2 ^ i = 2 ^ U := by exact_mod_cast this
  linarith

lemma sum_succ {U i : ℕ} {M : Type*} [AddCommMonoid M] (G : (Fin (i+1) → BinaryVector U) → M) :
    ∑ t ∈ Ind U (i+1), G t = ∑ v ∈ Ind U i, ∑ w ∈ nextVectors v, G (Fin.snoc v w) := by
  classical
  rw [Finset.sum_sigma']
  refine Finset.sum_bij' (fun t _ => ⟨Fin.init t, t (Fin.last i)⟩)
    (fun p _ => Fin.snoc p.1 p.2) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    rw [mem_Ind] at ht
    have := ht
    rw [← Fin.snoc_init_self t, linearIndependent_finSnoc] at this
    simp only [Finset.mem_sigma, mem_Ind, nextVectors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact this
  · rintro ⟨v, w⟩ hp
    simp only [Finset.mem_sigma, mem_Ind, nextVectors, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rw [mem_Ind, linearIndependent_finSnoc]
    exact hp
  · intro t _; simp
  · rintro ⟨v, w⟩ _; simp
  · intro t _; simp


noncomputable def avgI (U i : ℕ) (G : (Fin i → BinaryVector U) → ℝ) : ℝ :=
  (∑ t ∈ Ind U i, G t) / ((Ind U i).card : ℝ)

lemma card_Ind_succ (U i : ℕ) :
    ((Ind U (i + 1)).card : ℝ) = (Ind U i).card * (2 ^ U - 2 ^ i) := by
  have h := sum_succ (U := U) (i := i) (M := ℝ) (fun _ => 1)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  rw [h]
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun v hv => ?_)
  rw [mem_Ind] at hv
  simpa using card_next hv

lemma avg_succ (U i : ℕ) (G : (Fin (i + 1) → BinaryVector U) → ℝ) :
    avgI U (i + 1) G = avgI U i
      (fun v => (∑ w ∈ nextVectors v, G (Fin.snoc v w)) / (2 ^ U - 2 ^ i)) := by
  unfold avgI
  rw [sum_succ, card_Ind_succ, div_mul_eq_div_div_swap, Finset.sum_div]

lemma avgI_mono {U i : ℕ} {F H : (Fin i → BinaryVector U) → ℝ}
    (h : ∀ v ∈ Ind U i, F v ≤ H v) : avgI U i F ≤ avgI U i H := by
  unfold avgI
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum h) (Nat.cast_nonneg _)

lemma avgI_const_mul {U i : ℕ} (c : ℝ) (F : (Fin i → BinaryVector U) → ℝ) :
    avgI U i (fun v => c * F v) = c * avgI U i F := by
  unfold avgI
  rw [← Finset.mul_sum, mul_div_assoc]

lemma kp_pos {U i : ℕ} (S : Finset (BinaryVector U)) (lam : ℝ) (v : Fin i → BinaryVector U) :
    0 < kernelPotential S lam v := by
  unfold kernelPotential
  refine div_pos (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty) (by positivity)

lemma step {U i : ℕ} (hi : i < U) (S : Finset (BinaryVector U)) (lam : ℝ)
    (v : Fin i → BinaryVector U) (hv : LinearIndependent (ZMod 2) v) :
    (∑ w ∈ nextVectors v, Real.log (kernelPotential S lam (Fin.snoc v w))) / (2 ^ U - 2 ^ i)
      ≤ 2 * Real.log (kernelPotential S lam v) := by
  have hcn : ((nextVectors v).card : ℝ) = 2 ^ U - 2 ^ i := card_next hv
  have hpos : (0 : ℝ) < 2 ^ U - 2 ^ i := by
    have : (2 : ℝ) ^ i < 2 ^ U := pow_lt_pow_right₀ (by norm_num) hi
    linarith
  have hcs := conditional_squaring hi S lam v hv
  set Φ := kernelPotential S lam v with hΦ
  have hΦpos : 0 < Φ := kp_pos S lam v
  set A := Φ ^ 2 with hA
  have hApos : 0 < A := by positivity
  rw [hcn] at hcs
  have hT : ∑ w ∈ nextVectors v, kernelPotential S lam (Fin.snoc v w) ≤ A * (2 ^ U - 2 ^ i) := by
    rwa [div_le_iff₀ hpos] at hcs
  have hL : ∑ w ∈ nextVectors v, Real.log (kernelPotential S lam (Fin.snoc v w)) ≤
      ∑ w ∈ nextVectors v, (Real.log A - 1 + kernelPotential S lam (Fin.snoc v w) / A) := by
    refine Finset.sum_le_sum (fun w _ => ?_)
    have hw := kp_pos S lam (Fin.snoc v w : Fin (i+1) → BinaryVector U)
    have := Real.log_le_sub_one_of_pos (div_pos hw hApos)
    rw [Real.log_div hw.ne' hApos.ne'] at this
    linarith
  rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.sum_div, nsmul_eq_mul, hcn] at hL
  have hT' : (∑ w ∈ nextVectors v, kernelPotential S lam (Fin.snoc v w)) / A ≤ 2 ^ U - 2 ^ i := by
    rw [div_le_iff₀ hApos]; linarith
  have hlogA : Real.log A = 2 * Real.log Φ := by
    rw [hA, Real.log_pow]; norm_num
  rw [div_le_iff₀ hpos, ← hlogA]
  nlinarith [hL, hT']

lemma avg_chain (U : ℕ) (S : Finset (BinaryVector U)) (lam : ℝ) :
    ∀ k, k ≤ U → avgI U k (fun t => Real.log (kernelPotential S lam t)) ≤
      2 ^ k * avgI U 0 (fun t => Real.log (kernelPotential S lam t)) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    rw [avg_succ]
    calc _ ≤ avgI U i (fun v => 2 * Real.log (kernelPotential S lam v)) := by
          refine avgI_mono (fun v hv => ?_)
          rw [mem_Ind] at hv
          exact step (by omega) S lam v hv
      _ = 2 * avgI U i (fun t => Real.log (kernelPotential S lam t)) := avgI_const_mul _ _
      _ ≤ 2 * (2 ^ i * avgI U 0 (fun t => Real.log (kernelPotential S lam t))) := by
          have := ih (by omega); linarith
      _ = _ := by ring

lemma Ind_zero (U : ℕ) : Ind U 0 = Finset.univ := by
  classical
  ext v; simp only [mem_Ind, Finset.mem_univ, iff_true]
  exact linearIndependent_empty_type

lemma avgI_zero (U : ℕ) (G : (Fin 0 → BinaryVector U) → ℝ) (v0 : Fin 0 → BinaryVector U) :
    avgI U 0 G = G v0 := by
  unfold avgI
  rw [Ind_zero]
  simp [Unique.eq_default v0]

lemma phi0 (U : ℕ) (S : Finset (BinaryVector U)) (lam : ℝ) (v0 : Fin 0 → BinaryVector U) :
    Real.log (kernelPotential S lam v0) ≤
      (S.card : ℝ) * (Real.exp lam - lam - 1) / 2 ^ U := by
  classical
  set c : ℝ := (S.card : ℝ) / 2 ^ U with hc
  have hspan : tupleSpan v0 = ⊥ := by
    unfold tupleSpan
    rw [Set.range_eq_empty, Submodule.span_empty]
  have hload : ∀ x : BinaryVector U, centeredCosetLoad S v0 x = (if x ∈ S then 1 else 0) - c := by
    intro x
    unfold centeredCosetLoad
    rw [hspan]
    simp only [Submodule.mem_bot, sub_eq_zero, Nat.sub_zero, hc]
    congr 1
    by_cases hx : x ∈ S
    · rw [if_pos hx]
      have : S.filter (fun s => s = x) = {x} := by
        ext s; simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨_, h⟩; exact h
        · rintro rfl; exact ⟨hx, rfl⟩
      rw [this]; simp
    · rw [if_neg hx]
      have : S.filter (fun s => s = x) = ∅ := by
        ext s; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        rintro hs rfl; exact hx hs
      rw [this]; simp
  have hsum : ∑ x : BinaryVector U, Real.exp (lam * centeredCosetLoad S v0 x) =
      (S.card : ℝ) * Real.exp (lam * (1 - c)) +
        (2 ^ U - (S.card : ℝ)) * Real.exp (lam * (0 - c)) := by
    simp_rw [hload]
    have : ∀ x : BinaryVector U, Real.exp (lam * ((if x ∈ S then (1:ℝ) else 0) - c)) =
        if x ∈ S then Real.exp (lam * (1 - c)) else Real.exp (lam * (0 - c)) := by
      intro x; split_ifs <;> rfl
    simp_rw [this]
    rw [Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.univ_inter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    congr 2
    have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (BinaryVector U)))
      (fun x => x ∈ S)
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter] at h1
    have h3 : (Finset.univ : Finset (BinaryVector U)).card = 2 ^ U := by simp
    rw [h3] at h1
    have h5 : (S.card : ℝ) + ((Finset.univ.filter (fun x : BinaryVector U => x ∉ S)).card : ℝ) = 2 ^ U := by
      exact_mod_cast h1
    linarith
  have hΦ : kernelPotential S lam v0 = Real.exp (-(lam * c)) *
      (1 + (S.card : ℝ) * (Real.exp lam - 1) / 2 ^ U) := by
    unfold kernelPotential
    rw [hsum]
    have e1 : Real.exp (lam * (1 - c)) = Real.exp (-(lam * c)) * Real.exp lam := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (lam * (0 - c)) = Real.exp (-(lam * c)) := by
      congr 1; ring
    rw [e1, e2]
    field_simp
    ring
  have hpos := kp_pos S lam v0
  rw [hΦ] at hpos ⊢
  have hy : 0 < 1 + (S.card : ℝ) * (Real.exp lam - 1) / 2 ^ U :=
    (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp hpos
  rw [Real.log_mul (Real.exp_pos _).ne' hy.ne', Real.log_exp]
  have := Real.log_le_sub_one_of_pos hy
  have e3 : lam * c = (S.card : ℝ) * lam / 2 ^ U := by rw [hc]; ring
  have e4 : (S.card : ℝ) * (Real.exp lam - lam - 1) / 2 ^ U =
      (S.card : ℝ) * (Real.exp lam - 1) / 2 ^ U - (S.card : ℝ) * lam / 2 ^ U := by ring
  rw [e4, ← e3]
  linarith

theorem tuple_avg_bound {U k : ℕ} (hk : k ≤ U) (S : Finset (BinaryVector U)) (lam : ℝ) :
    avgI U k (fun t => Real.log (kernelPotential S lam t)) ≤
      2 ^ k * ((S.card : ℝ) * (Real.exp lam - lam - 1) / 2 ^ U) := by
  refine (avg_chain U S lam k hk).trans ?_
  rw [avgI_zero U _ (fun i => i.elim0)]
  exact mul_le_mul_of_nonneg_left (phi0 U S lam _) (by positivity)

end LinearHashingPoissonesque.Dev.PotIter
end

section
set_option autoImplicit false

namespace LinearHashingPoissonesque.Dev.PotBridge
open LinearHashingPoissonesque.ExpectedLoads LinearHashingPoissonesque.Dev.PotIter


/-- the centered potential, as a function of the subspace -/
noncomputable def PsiK {U : ℕ} (S : Finset (BinaryVector U)) (lam : ℝ) (k : ℕ)
    (K : Submodule (ZMod 2) (BinaryVector U)) : ℝ := by
  classical
  exact Real.log ((∑ x : BinaryVector U, Real.exp (lam * (((S.filter (fun s => s - x ∈ K)).card : ℝ) -
    (S.card : ℝ) / (2 : ℝ) ^ (U - k)))) / (2 : ℝ) ^ U)

lemma fibre_card {U ell : ℕ} (hell : ell ≤ U) (h : BinaryVector U →ₗ[ZMod 2] (Fin ell → ZMod 2))
    (hs : Function.Surjective h) (y : Fin ell → ZMod 2) :
    (Finset.univ.filter (fun x => h x = y)).card = 2 ^ (U - ell) := by
  classical
  have h0 : (Finset.univ.filter (fun x => h x = y)).card =
      (Finset.univ.filter (fun x => h x = 0)).card := by
    exact AddMonoidHom.card_fiber_eq_of_mem_range h.toAddMonoidHom (by obtain ⟨x, hx⟩ := hs y; exact ⟨x, hx⟩) ⟨0, by simp⟩
  rw [h0]
  have h1 : (Finset.univ.filter (fun x => h x = 0)).card = Nat.card (LinearMap.ker h) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x; simp
  rw [h1, Module.natCard_eq_pow_finrank (K := ZMod 2)]
  have hr := LinearMap.finrank_range_add_finrank_ker h
  rw [LinearMap.range_eq_top.mpr hs, finrank_top] at hr
  simp only [Module.finrank_fin_fun] at hr
  simp only [Nat.card_zmod]
  congr 1
  omega


lemma logPot_eq {U ell : ℕ} (hell : ell ≤ U) (S : Finset (BinaryVector U)) (lam : ℝ)
    (h : BinaryVector U →ₗ[ZMod 2] (Fin ell → ZMod 2)) (hs : Function.Surjective h) :
    logPotential S (fun x => h x) lam = PsiK S lam (U - ell) (LinearMap.ker h) := by
  classical
  unfold logPotential PsiK
  have hB : (Fintype.card (Fin ell → ZMod 2) : ℝ) = 2 ^ ell := by simp
  rw [hB]
  have hUk : U - (U - ell) = ell := by omega
  rw [hUk]
  congr 1
  have hload : ∀ x : BinaryVector U,
      ((S.filter (fun s => s - x ∈ LinearMap.ker h)).card : ℝ) = (binLoad S (fun x => h x) (h x) : ℝ) := by
    intro x
    unfold binLoad
    congr 2
    ext s
    simp [LinearMap.mem_ker, sub_eq_zero]
  simp_rw [hload]
  set g : (Fin ell → ZMod 2) → ℝ := fun y =>
    Real.exp (lam * ((binLoad S (fun x => h x) y : ℝ) - (S.card : ℝ) / 2 ^ ell)) with hg
  have hsum : ∑ x : BinaryVector U, Real.exp (lam * ((binLoad S (fun x => h x) (h x) : ℝ) - (S.card : ℝ) / 2 ^ ell))
      = ∑ y : Fin ell → ZMod 2, (2 : ℝ) ^ (U - ell) * g y := by
    rw [← Finset.sum_fiberwise (Finset.univ : Finset (BinaryVector U)) (fun x => h x)
      (fun x => Real.exp (lam * ((binLoad S (fun x => h x) (h x) : ℝ) - (S.card : ℝ) / 2 ^ ell)))]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Finset.sum_congr rfl (g := fun _ => g y)]
    · rw [Finset.sum_const, nsmul_eq_mul]
      have := fibre_card hell h hs y
      rw [this]; push_cast; rfl
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp [hg, hx]
  rw [hsum, ← Finset.mul_sum]
  have : (2 : ℝ) ^ U = 2 ^ (U - ell) * 2 ^ ell := by
    rw [← pow_add]; congr 1; omega
  rw [this]
  field_simp


lemma avg_fibre {X Z : Type*} [DecidableEq Z] (A : Finset X) (p : X → Z) (P : Finset Z) (G : Z → ℝ)
    (hP : ∀ x ∈ A, p x ∈ P)
    (hsame : ∀ K ∈ P, ∀ K' ∈ P,
      (A.filter (fun x => p x = K)).card = (A.filter (fun x => p x = K')).card)
    (hpos : ∀ K ∈ P, 0 < (A.filter (fun x => p x = K)).card) :
    (∑ x ∈ A, G (p x)) / (A.card : ℝ) = (∑ K ∈ P, G K) / (P.card : ℝ) := by
  rcases P.eq_empty_or_nonempty with rfl | ⟨K0, hK0⟩
  · have : A = ∅ := Finset.eq_empty_of_forall_notMem (fun x hx => by simpa using hP x hx)
    simp [this]
  · set c := (A.filter (fun x => p x = K0)).card with hcdef
    have hc : ∀ K ∈ P, (A.filter fun x => p x = K).card = c := fun K hK => hsame K hK K0 hK0
    have h1 : ∑ x ∈ A, G (p x) = c * ∑ K ∈ P, G K := by
      rw [← Finset.sum_fiberwise_of_maps_to hP, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun K hK => ?_)
      rw [Finset.sum_congr rfl (g := fun _ => G K)
        (fun x hx => by rw [(Finset.mem_filter.1 hx).2]), Finset.sum_const, nsmul_eq_mul, hc K hK]
    have h2 : (A.card : ℝ) = c * P.card := by
      rw [Finset.card_eq_sum_card_fiberwise hP, Finset.sum_congr rfl hc]
      simp [mul_comm]
    have hc0 : (c : ℝ) ≠ 0 := by exact_mod_cast (hpos K0 hK0).ne'
    rw [h1, h2]
    rw [mul_div_mul_left _ _ hc0]

lemma tupleSpan_map {U k : ℕ} (g : BinaryVector U ≃ₗ[ZMod 2] BinaryVector U)
    (t : Fin k → BinaryVector U) :
    tupleSpan (fun j => g (t j)) = (tupleSpan t).map (g : BinaryVector U →ₗ[ZMod 2] BinaryVector U) := by
  unfold tupleSpan
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

lemma map_symm_map {U : ℕ} (g : BinaryVector U ≃ₗ[ZMod 2] BinaryVector U)
    (K : Submodule (ZMod 2) (BinaryVector U)) :
    (K.map (g : BinaryVector U →ₗ[ZMod 2] BinaryVector U)).map
      (g.symm : BinaryVector U →ₗ[ZMod 2] BinaryVector U) = K := by
  ext x
  simp only [Submodule.mem_map, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa using hz
  · intro hx
    exact ⟨g x, ⟨x, hx, rfl⟩, by simp⟩

lemma tuple_fibre_le {U k : ℕ} (K : Submodule (ZMod 2) (BinaryVector U))
    (g : BinaryVector U ≃ₗ[ZMod 2] BinaryVector U) :
    ((Ind U k).filter (fun t => tupleSpan t = K)).card ≤
      ((Ind U k).filter (fun t => tupleSpan t =
        K.map (g : BinaryVector U →ₗ[ZMod 2] BinaryVector U))).card := by
  classical
  refine Finset.card_le_card_of_injOn (fun t j => g (t j)) ?_ ?_
  · intro t ht
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_Ind] at ht ⊢
    refine ⟨?_, by rw [tupleSpan_map, ht.2]⟩
    exact ht.1.map' (g : BinaryVector U →ₗ[ZMod 2] BinaryVector U) (LinearEquiv.ker g)
  · intro t _ t' _ h
    funext j
    exact g.injective (congrFun h j)

lemma tuple_fibre_eq {U k : ℕ} (K K' : Submodule (ZMod 2) (BinaryVector U))
    (g : BinaryVector U ≃ₗ[ZMod 2] BinaryVector U)
    (hg : K.map (g : BinaryVector U →ₗ[ZMod 2] BinaryVector U) = K') :
    ((Ind U k).filter (fun t => tupleSpan t = K)).card =
      ((Ind U k).filter (fun t => tupleSpan t = K')).card := by
  subst hg
  refine le_antisymm (tuple_fibre_le K g) ?_
  have := tuple_fibre_le (U := U) (k := k) (K.map (g : BinaryVector U →ₗ[ZMod 2] BinaryVector U)) g.symm
  rwa [map_symm_map] at this

lemma exists_equiv_map {U : ℕ} (K K' : Submodule (ZMod 2) (BinaryVector U))
    (h : Module.finrank (ZMod 2) K = Module.finrank (ZMod 2) K') :
    ∃ g : BinaryVector U ≃ₗ[ZMod 2] BinaryVector U,
      K.map (g : BinaryVector U →ₗ[ZMod 2] BinaryVector U) = K' := by
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq (LinearEquiv.ofFinrankEq K K' h)
  refine ⟨g, ?_⟩
  ext y
  simp only [Submodule.mem_map, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have := hg ⟨x, hx⟩
    rw [← this]
    exact (LinearEquiv.ofFinrankEq K K' h ⟨x, hx⟩).2
  · intro hy
    refine ⟨((LinearEquiv.ofFinrankEq K K' h).symm ⟨y, hy⟩ : BinaryVector U), Subtype.coe_prop _, ?_⟩
    rw [← hg]
    simp


noncomputable instance instFintypeLinMap (U ell : ℕ) :
    Fintype (BinaryVector U →ₗ[ZMod 2] (Fin ell → ZMod 2)) := Fintype.ofFinite _

lemma finrank_ker_surj {U ell : ℕ} (h : BinaryVector U →ₗ[ZMod 2] (Fin ell → ZMod 2))
    (hs : Function.Surjective h) : Module.finrank (ZMod 2) (LinearMap.ker h) = U - ell := by
  have hr := LinearMap.finrank_range_add_finrank_ker h
  rw [LinearMap.range_eq_top.mpr hs, finrank_top] at hr
  simp only [Module.finrank_fin_fun] at hr
  omega

lemma surj_fibre_le {U ell : ℕ} (K : Submodule (ZMod 2) (BinaryVector U))
    (g : BinaryVector U ≃ₗ[ZMod 2] BinaryVector U) :
    ((Finset.univ.filter (fun h : BinaryVector U →ₗ[ZMod 2] (Fin ell → ZMod 2) =>
        Function.Surjective h ∧ LinearMap.ker h = K))).card ≤
      ((Finset.univ.filter (fun h : BinaryVector U →ₗ[ZMod 2] (Fin ell → ZMod 2) =>
        Function.Surjective h ∧ LinearMap.ker h =
          K.map (g : BinaryVector U →ₗ[ZMod 2] BinaryVector U)))).card := by
  classical
  refine Finset.card_le_card_of_injOn (fun h => h.comp (g.symm : BinaryVector U →ₗ[ZMod 2] BinaryVector U)) ?_ ?_
  · intro h hh
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hh ⊢
    refine ⟨hh.1.comp g.symm.surjective, ?_⟩
    ext x
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      Submodule.mem_map]
    constructor
    · intro hx
      refine ⟨g.symm x, ?_, by simp⟩
      rw [← hh.2]; exact hx
    · rintro ⟨y, hy, rfl⟩
      rw [← hh.2] at hy
      simpa using hy
  · intro h _ h' _ H
    refine LinearMap.ext (fun x => ?_)
    have := LinearMap.congr_fun H (g x)
    simpa using this

lemma surj_fibre_eq {U ell : ℕ} (K K' : Submodule (ZMod 2) (BinaryVector U))
    (g : BinaryVector U ≃ₗ[ZMod 2] BinaryVector U)
    (hg : K.map (g : BinaryVector U →ₗ[ZMod 2] BinaryVector U) = K') :
    ((Finset.univ.filter (fun h : BinaryVector U →ₗ[ZMod 2] (Fin ell → ZMod 2) =>
        Function.Surjective h ∧ LinearMap.ker h = K))).card =
      ((Finset.univ.filter (fun h : BinaryVector U →ₗ[ZMod 2] (Fin ell → ZMod 2) =>
        Function.Surjective h ∧ LinearMap.ker h = K'))).card := by
  subst hg
  refine le_antisymm (surj_fibre_le K g) ?_
  have := surj_fibre_le (U := U) (ell := ell) (K.map (g : BinaryVector U →ₗ[ZMod 2] BinaryVector U)) g.symm
  rwa [map_symm_map] at this

lemma tuple_fibre_pos {U k : ℕ} (K : Submodule (ZMod 2) (BinaryVector U))
    (hK : Module.finrank (ZMod 2) K = k) :
    0 < ((Ind U k).filter (fun t => tupleSpan t = K)).card := by
  classical
  apply Finset.card_pos.mpr
  let b := Module.finBasisOfFinrankEq (ZMod 2) K hK
  refine ⟨fun i => (b i : BinaryVector U), ?_⟩
  simp only [Finset.mem_filter, mem_Ind]
  refine ⟨?_, ?_⟩
  · exact b.linearIndependent.map' K.subtype K.ker_subtype
  · unfold tupleSpan
    have : Set.range (fun i => (b i : BinaryVector U)) = K.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]

lemma surj_fibre_pos {U ell : ℕ} (hell : ell ≤ U) (K : Submodule (ZMod 2) (BinaryVector U))
    (hK : Module.finrank (ZMod 2) K = U - ell) :
    0 < ((Finset.univ.filter (fun h : BinaryVector U →ₗ[ZMod 2] (Fin ell → ZMod 2) =>
        Function.Surjective h ∧ LinearMap.ker h = K))).card := by
  classical
  apply Finset.card_pos.mpr
  have hq := Submodule.finrank_quotient_add_finrank K
  simp only [Module.finrank_fin_fun] at hq
  have hfr : Module.finrank (ZMod 2) (BinaryVector U ⧸ K) =
      Module.finrank (ZMod 2) (Fin ell → ZMod 2) := by
    rw [Module.finrank_fin_fun]; omega
  let e := LinearEquiv.ofFinrankEq (BinaryVector U ⧸ K) (Fin ell → ZMod 2) hfr
  refine ⟨e.toLinearMap.comp K.mkQ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩⟩
  · exact e.surjective.comp K.mkQ_surjective
  · rw [LinearEquiv.ker_comp, Submodule.ker_mkQ]


theorem surj_avg_eq {U ell : ℕ} (hell : ell ≤ U)
    (G : Submodule (ZMod 2) (BinaryVector U) → ℝ) :
    LinMaxLoad.condAvgLin (ZMod 2) (BinaryVector U) ell (fun h => Function.Surjective h)
      (fun h => G (LinearMap.ker h)) = avgI U (U - ell) (fun t => G (tupleSpan t)) := by
  classical
  have : Fintype (Submodule (ZMod 2) (BinaryVector U)) := Fintype.ofFinite _
  set P : Finset (Submodule (ZMod 2) (BinaryVector U)) :=
    Finset.univ.filter (fun K => Module.finrank (ZMod 2) K = U - ell) with hPdef
  have hmem : ∀ K, K ∈ P ↔ Module.finrank (ZMod 2) K = U - ell := by
    intro K; simp [hPdef]
  have hX := avg_fibre (Finset.univ.filter
      (fun h : BinaryVector U →ₗ[ZMod 2] (Fin ell → ZMod 2) => Function.Surjective h))
    (fun h => LinearMap.ker h) P G ?_ ?_ ?_
  have hY := avg_fibre (Ind U (U - ell)) tupleSpan P G ?_ ?_ ?_
  · unfold LinMaxLoad.condAvgLin avgI
    convert hX.trans hY.symm using 3
    all_goals first | (ext; simp) | (congr 1; ext; simp)
  · intro t ht
    rw [mem_Ind] at ht
    rw [hmem]
    unfold tupleSpan
    rw [finrank_span_eq_card ht]; simp
  · intro K hK K' hK'
    rw [hmem] at hK hK'
    obtain ⟨g, hg⟩ := exists_equiv_map K K' (hK.trans hK'.symm)
    exact tuple_fibre_eq K K' g hg
  · intro K hK
    rw [hmem] at hK
    exact tuple_fibre_pos K hK
  · intro h hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh
    rw [hmem]
    exact finrank_ker_surj h hh
  · intro K hK K' hK'
    rw [hmem] at hK hK'
    obtain ⟨g, hg⟩ := exists_equiv_map K K' (hK.trans hK'.symm)
    simp only [Finset.filter_filter]
    exact surj_fibre_eq K K' g hg
  · intro K hK
    rw [hmem] at hK
    simp only [Finset.filter_filter]
    exact surj_fibre_pos hell K hK


theorem surj_avg_bound {U ell : ℕ} (hell : ell ≤ U) (S : Finset (BinaryVector U)) (lam : ℝ) :
    LinMaxLoad.condAvgLin (ZMod 2) (BinaryVector U) ell (fun h => Function.Surjective h)
      (fun h => logPotential S (fun x => h x) lam) ≤
    ((S.card : ℝ) / (2 : ℝ) ^ ell) * (Real.exp lam - lam - 1) := by
  classical
  have h1 : LinMaxLoad.condAvgLin (ZMod 2) (BinaryVector U) ell (fun h => Function.Surjective h)
      (fun h => logPotential S (fun x => h x) lam) =
      LinMaxLoad.condAvgLin (ZMod 2) (BinaryVector U) ell (fun h => Function.Surjective h)
      (fun h => PsiK S lam (U - ell) (LinearMap.ker h)) := by
    unfold LinMaxLoad.condAvgLin
    congr 1
    refine Finset.sum_congr rfl (fun h hh => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh
    exact logPot_eq hell S lam h hh
  rw [h1, surj_avg_eq hell (PsiK S lam (U - ell))]
  have h2 : avgI U (U - ell) (fun t => PsiK S lam (U - ell) (tupleSpan t)) =
      avgI U (U - ell) (fun t => Real.log (kernelPotential S lam t)) := by
    unfold avgI
    congr 1
  rw [h2]
  refine (tuple_avg_bound (Nat.sub_le U ell) S lam).trans (le_of_eq ?_)
  have : (2 : ℝ) ^ U = 2 ^ (U - ell) * 2 ^ ell := by
    rw [← pow_add]; congr 1; omega
  rw [this]
  field_simp

end LinearHashingPoissonesque.Dev.PotBridge
end

section
set_option autoImplicit false

namespace LinearHashingPoissonesque.Dev.PotPoisson
open LinearHashingPoissonesque.ExpectedLoads

lemma logPot_nonneg {A B : Type*} [Fintype B] [Nonempty B] (S : Finset A) (f : A → B) (lam : ℝ) :
    0 ≤ logPotential S f lam := by
  classical
  unfold logPotential
  have hB : (0 : ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
  have hsum : ∑ y : B, (binLoad S f y : ℝ) = S.card := by
    have h := Finset.card_eq_sum_card_fiberwise
      (s := S) (t := (Finset.univ : Finset B)) (f := f) (by intro a ha; simp)
    have : ∀ y : B, binLoad S f y = (S.filter (fun a => f a = y)).card := fun y => by
      unfold binLoad; congr
    simp only [this]
    exact_mod_cast h.symm
  apply Real.log_nonneg
  rw [le_div_iff₀ hB]
  have : ∑ y : B, (1 + lam * ((binLoad S f y : ℝ) - (S.card : ℝ) / (Fintype.card B : ℝ)))
      = Fintype.card B := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hsum]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring
  calc (1 : ℝ) * Fintype.card B = ∑ y : B, (1 + lam * ((binLoad S f y : ℝ) - (S.card : ℝ) / (Fintype.card B : ℝ))) := by
        rw [this]; ring
    _ ≤ _ := Finset.sum_le_sum (fun y _ => by
        have := Real.add_one_le_exp (lam * ((binLoad S f y : ℝ) - (S.card : ℝ) / (Fintype.card B : ℝ)))
        linarith)

end LinearHashingPoissonesque.Dev.PotPoisson

namespace LinearHashingPoissonesque.ExpectedLoads
open LinearHashingPoissonesque.Dev.PotPoisson LinearHashingPoissonesque.Dev.PotBridge in
theorem chk_potential_poisson {u ell m : ℕ} (hu : ell ≤ u) (hell : 1 ≤ ell) (hm : 1 ≤ m)
    (S : Finset (Fin u → ZMod 2)) (hS : S.card = m) (lam : ℝ) :
    LinMaxLoad.avgLin (ZMod 2) (Fin u → ZMod 2) ell
      (fun h => logPotential S h lam) ≤
    ((m : ℝ) / (2 : ℝ) ^ ell) * (Real.exp lam - lam - 1) := by
  classical
  have hBcard : Fintype.card (Fin ell → ZMod 2) = 2 ^ ell := by simp
  let f : LoadVector (Fin ell → ZMod 2) m → NNReal := fun w =>
    Real.toNNReal (Real.log ((∑ y, Real.exp (lam * ((w.1 y : ℝ) - (m : ℝ) / 2 ^ ell))) / 2 ^ ell))
  have hf : ∀ (U : ℕ) (S' : Finset (Fin U → ZMod 2)) (hS' : S'.card = m)
      (h : (Fin U → ZMod 2) →ₗ[ZMod 2] (Fin ell → ZMod 2)),
      ((f (labelledLoads S' hS' h) : NNReal) : ℝ) = logPotential S' (fun x => h x) lam := by
    intro U S' hS' h
    have : Nonempty (Fin ell → ZMod 2) := ⟨0⟩
    have hnn := logPot_nonneg S' (fun x => h x) lam
    have hlp : logPotential S' (fun x => h x) lam =
        Real.log ((∑ y, Real.exp (lam * ((binLoad S' (fun x => h x) y : ℝ) - (m : ℝ) / 2 ^ ell))) / 2 ^ ell) := by
      unfold logPotential
      rw [hBcard, hS']
      push_cast
      rfl
    rw [hlp] at hnn ⊢
    show ((Real.log ((∑ y, Real.exp (lam * ((binLoad S' (fun x => h x) y : ℝ) - (m : ℝ) / 2 ^ ell))) / 2 ^ ell)).toNNReal : ℝ) = _
    rw [Real.coe_toNNReal _ hnn]
  have ha : 0 ≤ ((m : ℝ) / (2 : ℝ) ^ ell) * (Real.exp lam - lam - 1) :=
    mul_nonneg (by positivity) (by linarith [Real.add_one_le_exp lam])
  have hr : 1 ≤ Fintype.card (ZMod 2) ^ ell := Nat.one_le_pow _ _ (by simp)
  have key := remove_surjectivity (ZMod 2) ell m 1 hell hm le_rfl hr f
    (((m : ℝ) / (2 : ℝ) ^ ell) * (Real.exp lam - lam - 1)) ha ?_ u hu S hS
  · have : (fun h : (Fin u → ZMod 2) →ₗ[ZMod 2] (Fin ell → ZMod 2) => ((f (labelledLoads S hS h) : NNReal) : ℝ)) =
        fun h => logPotential S (fun x => h x) lam := by
      funext h; exact hf u S hS h
    rw [this] at key
    exact key
  · refine (Set.Ici_infinite ell).mono (fun U hU => ⟨hU, fun S' hS' => ?_⟩)
    have : (fun h : (Fin U → ZMod 2) →ₗ[ZMod 2] (Fin ell → ZMod 2) => ((f (labelledLoads S' hS' h) : NNReal) : ℝ)) =
        fun h => logPotential S' (fun x => h x) lam := by
      funext h; exact hf U S' hS' h
    rw [this]
    have h2 := surj_avg_bound (U := U) (ell := ell) hU S' lam
    rwa [hS'] at h2

end LinearHashingPoissonesque.ExpectedLoads
end

theorem solution : type_of% @LinearHashingPoissonesque.ExpectedLoads.chk_potential_poisson := @LinearHashingPoissonesque.ExpectedLoads.chk_potential_poisson

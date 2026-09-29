-- Prove2me | solution 1 for MvPowerSeries.exists_rename_swap_eq_add_mul_X
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/e5628bc0-abbd-5edd-a6ce-8c1249bef807

import Definitions.Def_ModularCurve_UVCrossingChart
import Theorems.Thm_ModularCurve_UVCrossingModel_chartHom_C
import Theorems.Thm_ModularCurve_UVCrossingModel_range_chartHom_le_fixedSubring
import Theorems.Thm_ModularCurve_UVCrossingModel_U_notMem_fixedSubring
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X

universe u

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "uvCrossingIdeal UVCrossingModel uvSwapEquiv uvSwapEquiv_apply uvSwapEquiv_X_zero uvSwapEquiv_crossing UVCrossingModel.range_chartHom_le_fixedSubring"
p2m_open "ModularCurve"

theorem uvSwapEquiv_uvSwapEquiv {W : Type*} [CommRing W] (f : MvPowerSeries (Fin 2) W) :
    uvSwapEquiv (uvSwapEquiv f) = f := by
  have h := MvPowerSeries.renameEquiv_trans (R := W)
    (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 2) 1)
  rw [Equiv.swap_swap, MvPowerSeries.renameEquiv_refl] at h
  calc uvSwapEquiv (uvSwapEquiv f)
      = ((MvPowerSeries.renameEquiv W (Equiv.swap (0 : Fin 2) 1)).trans
          (MvPowerSeries.renameEquiv W (Equiv.swap (0 : Fin 2) 1))) f := rfl
    _ = (AlgEquiv.refl (R := W) (A₁ := MvPowerSeries (Fin 2) W)) f := by rw [h]
    _ = f := rfl

namespace UVCrossingModel
p2m_export "ModularCurve.UVCrossingModel" "sAmbient sAmbient_def chartHom chartHom_apply mk U const mk_surjective crossingSwap crossingSwap_mk fixedSubring mem_fixedSubring_iff chartHom_C range_chartHom_le_fixedSubring U_notMem_fixedSubring"
p2m_open "ModularCurve.UVCrossingModel"

theorem const_pow {W : Type*} [CommRing W] (π : W) (w : W) (n : ℕ) : const π (w ^ n) = const π w ^ n := by
  show mk π (MvPowerSeries.C (w ^ n)) = mk π (MvPowerSeries.C w) ^ n
  rw [map_pow, map_pow]

end UVCrossingModel

end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "uvCrossingIdeal UVCrossingModel uvSwapEquiv uvSwapEquiv_apply uvSwapEquiv_X_zero uvSwapEquiv_crossing UVCrossingModel.range_chartHom_le_fixedSubring"
p2m_open "ModularCurve"

namespace SymmetricTwoVars

noncomputable section

open MvPowerSeries

variable {W : Type u} [CommRing W]

def pairIdx (i j : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) j

theorem pairIdx_def (i j : ℕ) :
    pairIdx i j = Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) j := rfl

@[scoped simp] theorem pairIdx_apply_zero (i j : ℕ) : pairIdx i j 0 = i := by
  rw [pairIdx_def, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (by decide), add_zero]

@[scoped simp] theorem pairIdx_apply_one (i j : ℕ) : pairIdx i j 1 = j := by
  rw [pairIdx_def, Finsupp.add_apply, Finsupp.single_eq_of_ne (by decide),
    Finsupp.single_eq_same, zero_add]

theorem eq_pairIdx (d : Fin 2 →₀ ℕ) : d = pairIdx (d 0) (d 1) := by
  ext t
  revert t
  rw [Fin.forall_fin_two]
  exact ⟨(pairIdx_apply_zero _ _).symm, (pairIdx_apply_one _ _).symm⟩

theorem pairIdx_injEq {i j k l : ℕ} : pairIdx i j = pairIdx k l ↔ i = k ∧ j = l := by
  constructor
  · intro h
    constructor
    · simpa using DFunLike.congr_fun h 0
    · simpa using DFunLike.congr_fun h 1
  · rintro ⟨rfl, rfl⟩
    rfl

theorem pairIdx_add (i j k l : ℕ) :
    pairIdx i j + pairIdx k l = pairIdx (i + k) (j + l) := by
  ext t
  revert t
  rw [Fin.forall_fin_two]
  constructor <;> simp

theorem pairIdx_le_iff {i j k l : ℕ} : pairIdx k l ≤ pairIdx i j ↔ k ≤ i ∧ l ≤ j := by
  rw [Finsupp.le_def]
  rw [Fin.forall_fin_two]
  simp

theorem pairIdx_tsub (i j k l : ℕ) :
    pairIdx i j - pairIdx k l = pairIdx (i - k) (j - l) := by
  ext t
  revert t
  rw [Fin.forall_fin_two]
  constructor <;> simp [Finsupp.tsub_apply]

theorem mapDomain_swap_pairIdx (i j : ℕ) :
    Finsupp.mapDomain (⇑(Equiv.swap (0 : Fin 2) 1)) (pairIdx i j) = pairIdx j i := by
  rw [pairIdx_def, Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single,
    Equiv.swap_apply_left, Equiv.swap_apply_right, pairIdx_def]
  exact add_comm _ _

def SwapInvariant (f : MvPowerSeries (Fin 2) W) : Prop :=
  MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) f = f

theorem swapInvariant_of {f : MvPowerSeries (Fin 2) W}
    (h : MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) f = f) : SwapInvariant f := h

theorem SwapInvariant.rename_eq {f : MvPowerSeries (Fin 2) W} (hf : SwapInvariant f) :
    MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) f = f := hf

theorem coeff_rename_swap (f : MvPowerSeries (Fin 2) W) (d : Fin 2 →₀ ℕ) :
    coeff d (MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) f)
      = coeff (Finsupp.mapDomain (⇑(Equiv.swap (0 : Fin 2) 1)) d) f := by
  have hcomp : (⇑(Equiv.swap (0 : Fin 2) 1)) ∘ (⇑(Equiv.swap (0 : Fin 2) 1)) = id := by
    funext x
    exact Equiv.swap_apply_self _ _ x
  have h := MvPowerSeries.coeff_embDomain_rename (Equiv.swap (0 : Fin 2) 1).toEmbedding f
    (Finsupp.mapDomain (⇑(Equiv.swap (0 : Fin 2) 1)) d)
  rw [Finsupp.embDomain_eq_mapDomain] at h
  simp only [Equiv.coe_toEmbedding] at h
  rw [← Finsupp.mapDomain_comp, hcomp, Finsupp.mapDomain_id] at h
  exact h

theorem swapInvariant_iff_coeff (f : MvPowerSeries (Fin 2) W) :
    SwapInvariant f ↔ ∀ i j : ℕ, coeff (pairIdx j i) f = coeff (pairIdx i j) f := by
  constructor
  · intro hf i j
    conv_rhs => rw [← hf.rename_eq]
    rw [coeff_rename_swap, mapDomain_swap_pairIdx]
  · intro h
    apply MvPowerSeries.ext
    intro d
    obtain ⟨i, j, rfl⟩ : ∃ i j, d = pairIdx i j := ⟨d 0, d 1, eq_pairIdx d⟩
    rw [coeff_rename_swap, mapDomain_swap_pairIdx]
    exact h i j

protected theorem SwapInvariant.sub {f g : MvPowerSeries (Fin 2) W}
    (hf : SwapInvariant f) (hg : SwapInvariant g) : SwapInvariant (f - g) := by
  apply swapInvariant_of
  rw [map_sub, hf.rename_eq, hg.rename_eq]

def elemSym1 : MvPowerSeries (Fin 2) W := MvPowerSeries.X 0 + MvPowerSeries.X 1

theorem elemSym1_def :
    elemSym1 (W := W) = MvPowerSeries.X 0 + MvPowerSeries.X 1 := rfl

def elemSym2 : MvPowerSeries (Fin 2) W := MvPowerSeries.X 0 * MvPowerSeries.X 1

theorem elemSym2_def :
    elemSym2 (W := W) = MvPowerSeries.X 0 * MvPowerSeries.X 1 := rfl

def elemSymPair : Fin 2 → MvPowerSeries (Fin 2) W := ![elemSym1, elemSym2]

theorem elemSymPair_def :
    elemSymPair (W := W) = ![elemSym1, elemSym2] := rfl

@[scoped simp] theorem elemSymPair_zero : elemSymPair (W := W) 0 = elemSym1 := rfl

@[scoped simp] theorem elemSymPair_one : elemSymPair (W := W) 1 = elemSym2 := rfl

theorem constantCoeff_elemSym1 :
    MvPowerSeries.constantCoeff (elemSym1 (W := W)) = 0 := by
  rw [elemSym1_def, map_add, MvPowerSeries.constantCoeff_X, MvPowerSeries.constantCoeff_X,
    add_zero]

theorem constantCoeff_elemSym2 :
    MvPowerSeries.constantCoeff (elemSym2 (W := W)) = 0 := by
  rw [elemSym2_def, map_mul, MvPowerSeries.constantCoeff_X, zero_mul]

theorem elemSym2_eq_monomial :
    elemSym2 (W := W) = MvPowerSeries.monomial (pairIdx 1 1) 1 := by
  rw [elemSym2_def, MvPowerSeries.X_def, MvPowerSeries.X_def,
    MvPowerSeries.monomial_mul_monomial, one_mul]
  rfl

theorem elemSym2_pow (q : ℕ) :
    elemSym2 (W := W) ^ q = MvPowerSeries.monomial (pairIdx q q) 1 := by
  rw [elemSym2_def, mul_pow, MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq,
    MvPowerSeries.monomial_mul_monomial, one_mul]
  rfl

theorem X_zero_eq_monomial :
    (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) W)
      = MvPowerSeries.monomial (pairIdx 1 0) 1 := by
  rw [MvPowerSeries.X_def]
  congr 1
  rw [pairIdx_def, Finsupp.single_zero, add_zero]

theorem coeff_monomial_pairIdx (i j k l : ℕ) (a : W) :
    coeff (pairIdx i j) (MvPowerSeries.monomial (pairIdx k l) a)
      = if i = k ∧ j = l then a else 0 := by
  classical
  rw [MvPowerSeries.coeff_monomial]
  simp only [pairIdx_injEq]

theorem swapInvariant_elemSym1 : SwapInvariant (elemSym1 (W := W)) := by
  apply swapInvariant_of
  rw [elemSym1_def, map_add, MvPowerSeries.rename_X, MvPowerSeries.rename_X,
    Equiv.swap_apply_left, Equiv.swap_apply_right, add_comm]

theorem swapInvariant_elemSym2 : SwapInvariant (elemSym2 (W := W)) := by
  apply swapInvariant_of
  rw [elemSym2_def, map_mul, MvPowerSeries.rename_X, MvPowerSeries.rename_X,
    Equiv.swap_apply_left, Equiv.swap_apply_right, mul_comm]

theorem coeff_elemSym1_pow (p i j : ℕ) :
    coeff (pairIdx i j) (elemSym1 (W := W) ^ p)
      = if i + j = p then (p.choose i : W) else 0 := by
  classical
  rw [elemSym1_def, add_pow, map_sum]
  have h1 : ∀ k ∈ Finset.range (p + 1),
      coeff (pairIdx i j)
          ((MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) W) ^ k
            * MvPowerSeries.X 1 ^ (p - k) * ((p.choose k : ℕ) : MvPowerSeries (Fin 2) W))
        = if i = k ∧ j = p - k then (p.choose k : W) else 0 := by
    intro k _
    rw [MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial,
      one_mul,
      ← map_natCast (MvPowerSeries.C : W →+* MvPowerSeries (Fin 2) W) (p.choose k),
      MvPowerSeries.coeff_mul_C]
    rw [show (Finsupp.single (0 : Fin 2) k + Finsupp.single (1 : Fin 2) (p - k))
        = pairIdx k (p - k) from rfl]
    rw [coeff_monomial_pairIdx, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_congr rfl h1]
  by_cases hij : i + j = p
  · rw [if_pos hij,
      Finset.sum_eq_single_of_mem i (Finset.mem_range.mpr (by omega))
        (fun k _ hk => if_neg fun hc => hk hc.1.symm),
      if_pos ⟨rfl, by omega⟩]
  · rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro k hk
    apply if_neg
    rintro ⟨rfl, rfl⟩
    exact hij (by have := Finset.mem_range.mp hk; omega)

theorem hasSubst_elemSym1 : PowerSeries.HasSubst (elemSym1 (W := W)) :=
  PowerSeries.HasSubst.of_constantCoeff_zero constantCoeff_elemSym1

def substS (φ : PowerSeries W) : MvPowerSeries (Fin 2) W :=
  PowerSeries.subst (elemSym1 (W := W)) φ

theorem substS_def (φ : PowerSeries W) :
    substS φ = PowerSeries.subst (elemSym1 (W := W)) φ := rfl

theorem coeff_substS (φ : PowerSeries W) (i j : ℕ) :
    coeff (pairIdx i j) (substS φ)
      = ((i + j).choose i : W) * PowerSeries.coeff (i + j) φ := by
  rw [substS_def, PowerSeries.coeff_subst hasSubst_elemSym1]
  rw [finsum_eq_single _ (i + j)
    (fun d hd => by rw [coeff_elemSym1_pow, if_neg fun hc => hd hc.symm, smul_zero])]
  rw [coeff_elemSym1_pow, if_pos rfl, smul_eq_mul, mul_comm]

theorem swapInvariant_substS (φ : PowerSeries W) : SwapInvariant (substS φ) := by
  rw [swapInvariant_iff_coeff]
  intro i j
  rw [coeff_substS, coeff_substS, Nat.add_comm j i]
  have h := Nat.choose_symm (Nat.le_add_right i j)
  rw [show i + j - i = j by omega] at h
  rw [h]

def bottomSeries (f : MvPowerSeries (Fin 2) W) : PowerSeries W :=
  PowerSeries.mk fun n => coeff (pairIdx n 0) f

@[scoped simp] theorem coeff_bottomSeries (f : MvPowerSeries (Fin 2) W) (n : ℕ) :
    PowerSeries.coeff n (bottomSeries f) = coeff (pairIdx n 0) f :=
  PowerSeries.coeff_mk _ _

theorem bottomSeries_substS (φ : PowerSeries W) : bottomSeries (substS φ) = φ := by
  ext n
  rw [coeff_bottomSeries, coeff_substS, Nat.add_zero, Nat.choose_self, Nat.cast_one, one_mul]

private def _root_.ModularCurve.SymmetricTwoVars.shiftDiag (f : MvPowerSeries (Fin 2) W) : MvPowerSeries (Fin 2) W :=
  fun d => coeff (d + pairIdx 1 1) f

p2m_export "ModularCurve.SymmetricTwoVars" "shiftDiag"
theorem coeff_shiftDiag (f : MvPowerSeries (Fin 2) W) (d : Fin 2 →₀ ℕ) :
    coeff d (shiftDiag f) = coeff (d + pairIdx 1 1) f := rfl

protected theorem SwapInvariant.shiftDiag {f : MvPowerSeries (Fin 2) W}
    (hf : SwapInvariant f) : SwapInvariant (shiftDiag f) := by
  rw [swapInvariant_iff_coeff]
  intro i j
  rw [coeff_shiftDiag, coeff_shiftDiag, pairIdx_add, pairIdx_add]
  exact (swapInvariant_iff_coeff f).mp hf (i + 1) (j + 1)

theorem elemSym2_mul_shiftDiag {f : MvPowerSeries (Fin 2) W} (hf : SwapInvariant f)
    (h0 : ∀ n, coeff (pairIdx n 0) f = 0) :
    elemSym2 * shiftDiag f = f := by
  classical
  apply MvPowerSeries.ext
  intro d
  obtain ⟨i, j, rfl⟩ : ∃ i j, d = pairIdx i j := ⟨d 0, d 1, eq_pairIdx d⟩
  rw [elemSym2_eq_monomial, MvPowerSeries.coeff_monomial_mul]
  by_cases h : pairIdx 1 1 ≤ pairIdx i j
  · rw [if_pos h, one_mul, pairIdx_tsub, coeff_shiftDiag, pairIdx_add]
    obtain ⟨h1, h2⟩ := pairIdx_le_iff.mp h
    rw [show i - 1 + 1 = i by omega, show j - 1 + 1 = j by omega]
  · rw [if_neg h]
    have hij : i = 0 ∨ j = 0 := by
      rcases Nat.eq_zero_or_pos i with hi | hi
      · exact Or.inl hi
      rcases Nat.eq_zero_or_pos j with hj | hj
      · exact Or.inr hj
      exact absurd (pairIdx_le_iff.mpr ⟨hi, hj⟩) h
    rcases hij with rfl | rfl
    · rw [(swapInvariant_iff_coeff f).mp hf j 0]
      exact (h0 j).symm
    · exact (h0 i).symm

def newton (f : MvPowerSeries (Fin 2) W) : ℕ → MvPowerSeries (Fin 2) W
  | 0 => f
  | n + 1 => shiftDiag (newton f n - substS (bottomSeries (newton f n)))

theorem newton_zero (f : MvPowerSeries (Fin 2) W) : newton f 0 = f := rfl

theorem newton_succ (f : MvPowerSeries (Fin 2) W) (n : ℕ) :
    newton f (n + 1) = shiftDiag (newton f n - substS (bottomSeries (newton f n))) := rfl

theorem swapInvariant_newton {f : MvPowerSeries (Fin 2) W} (hf : SwapInvariant f) (n : ℕ) :
    SwapInvariant (newton f n) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact (ih.sub (swapInvariant_substS _)).shiftDiag

theorem newton_step {f : MvPowerSeries (Fin 2) W} (hf : SwapInvariant f) (n : ℕ) :
    newton f n
      = substS (bottomSeries (newton f n)) + elemSym2 * newton f (n + 1) := by
  have hsym : SwapInvariant (newton f n - substS (bottomSeries (newton f n))) :=
    (swapInvariant_newton hf n).sub (swapInvariant_substS _)
  have h0 : ∀ m, coeff (pairIdx m 0)
      (newton f n - substS (bottomSeries (newton f n))) = 0 := by
    intro m
    rw [map_sub, coeff_substS, coeff_bottomSeries, Nat.add_zero, Nat.choose_self,
      Nat.cast_one, one_mul, sub_self]
  have hdiv := elemSym2_mul_shiftDiag hsym h0
  rw [newton_succ, hdiv]
  ring

theorem newton_telescope {f : MvPowerSeries (Fin 2) W} (hf : SwapInvariant f) (K : ℕ) :
    f = (∑ q ∈ Finset.range K, substS (bottomSeries (newton f q)) * elemSym2 ^ q)
        + elemSym2 ^ K * newton f K := by
  induction K with
  | zero => simp [newton_zero]
  | succ K ih =>
    conv_lhs => rw [ih, newton_step hf K]
    rw [Finset.sum_range_succ]
    ring

theorem hasSubst_elemSymPair : MvPowerSeries.HasSubst (elemSymPair (W := W)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero
    (Fin.forall_fin_two.mpr
      ⟨by rw [elemSymPair_zero]; exact constantCoeff_elemSym1,
       by rw [elemSymPair_one]; exact constantCoeff_elemSym2⟩)

theorem finsupp_prod_elemSymPair (e : Fin 2 →₀ ℕ) :
    (e.prod fun s n => elemSymPair (W := W) s ^ n)
      = elemSym1 ^ (e 0) * elemSym2 ^ (e 1) := by
  rw [Finsupp.prod_fintype _ _ fun i => pow_zero _, Fin.prod_univ_two,
    elemSymPair_zero, elemSymPair_one]

theorem coeff_elemSym1_pow_mul_elemSym2_pow (p q i j : ℕ) :
    coeff (pairIdx i j) (elemSym1 (W := W) ^ p * elemSym2 ^ q)
      = if q ≤ i ∧ q ≤ j then
          (if (i - q) + (j - q) = p then (p.choose (i - q) : W) else 0)
        else 0 := by
  classical
  rw [elemSym2_pow, MvPowerSeries.coeff_mul_monomial, mul_one, pairIdx_tsub,
    coeff_elemSym1_pow]
  simp only [pairIdx_le_iff]

theorem coeff_subst_elemSymPair (h : MvPowerSeries (Fin 2) W) (i j : ℕ) :
    coeff (pairIdx i j) (MvPowerSeries.subst elemSymPair h)
      = ∑ q ∈ Finset.range (min i j + 1),
          ((i + j - 2 * q).choose (i - q) : W) * coeff (pairIdx (i + j - 2 * q) q) h := by
  classical
  rw [MvPowerSeries.coeff_subst hasSubst_elemSymPair]
  have hprod : ∀ e : Fin 2 →₀ ℕ,
      coeff (pairIdx i j) (e.prod fun s n => elemSymPair (W := W) s ^ n)
        = if e 1 ≤ i ∧ e 1 ≤ j then
            (if (i - e 1) + (j - e 1) = e 0 then ((e 0).choose (i - e 1) : W) else 0)
          else 0 := by
    intro e
    rw [finsupp_prod_elemSymPair, coeff_elemSym1_pow_mul_elemSym2_pow]
  have hsupp : (Function.support fun e : Fin 2 →₀ ℕ =>
      coeff e h • coeff (pairIdx i j) (e.prod fun s n => elemSymPair (W := W) s ^ n))
      ⊆ ↑((Finset.range (min i j + 1)).image fun q => pairIdx (i + j - 2 * q) q) := by
    intro e he
    rw [Function.mem_support] at he
    have hco : coeff (pairIdx i j) (e.prod fun s n => elemSymPair (W := W) s ^ n) ≠ 0 := by
      intro hzero
      exact he (by rw [hzero, smul_zero])
    rw [hprod e] at hco
    by_cases hc1 : e 1 ≤ i ∧ e 1 ≤ j
    swap
    · rw [if_neg hc1] at hco
      exact absurd rfl hco
    rw [if_pos hc1] at hco
    by_cases hc2 : (i - e 1) + (j - e 1) = e 0
    swap
    · rw [if_neg hc2] at hco
      exact absurd rfl hco
    rw [Finset.coe_image, Set.mem_image]
    refine ⟨e 1, ?_, ?_⟩
    · rw [Finset.mem_coe, Finset.mem_range]
      omega
    · rw [show i + j - 2 * (e 1) = e 0 by omega]
      exact (eq_pairIdx e).symm
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  rw [Finset.sum_image
    (fun q1 _ q2 _ hq => by simpa using (pairIdx_injEq.mp hq).2)]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.mem_range] at hq
  have hqi : q ≤ i := by omega
  have hqj : q ≤ j := by omega
  rw [hprod (pairIdx (i + j - 2 * q) q)]
  simp only [pairIdx_apply_zero, pairIdx_apply_one]
  rw [if_pos ⟨hqi, hqj⟩, if_pos (by omega), smul_eq_mul, mul_comm]

def newtonAssembled (f : MvPowerSeries (Fin 2) W) : MvPowerSeries (Fin 2) W :=
  fun d => coeff (pairIdx (d 0) 0) (newton f (d 1))

theorem coeff_newtonAssembled (f : MvPowerSeries (Fin 2) W) (a b : ℕ) :
    coeff (pairIdx a b) (newtonAssembled f) = coeff (pairIdx a 0) (newton f b) := by
  have h : coeff (pairIdx a b) (newtonAssembled f)
      = coeff (pairIdx ((pairIdx a b) 0) 0) (newton f ((pairIdx a b) 1)) := rfl
  rw [h, pairIdx_apply_zero, pairIdx_apply_one]

theorem subst_newtonAssembled {f : MvPowerSeries (Fin 2) W} (hf : SwapInvariant f) :
    MvPowerSeries.subst elemSymPair (newtonAssembled f) = f := by
  classical
  apply MvPowerSeries.ext
  intro d
  obtain ⟨i, j, rfl⟩ : ∃ i j, d = pairIdx i j := ⟨d 0, d 1, eq_pairIdx d⟩
  have hR : coeff (pairIdx i j) f
      = ∑ q ∈ Finset.range (min i j + 1),
          ((i + j - 2 * q).choose (i - q) : W)
            * coeff (pairIdx (i + j - 2 * q) 0) (newton f q) := by
    conv_lhs => rw [newton_telescope hf (min i j + 1)]
    rw [map_add, map_sum]
    have hrem : coeff (pairIdx i j)
        (elemSym2 ^ (min i j + 1) * newton f (min i j + 1)) = 0 := by
      rw [elemSym2_pow, MvPowerSeries.coeff_monomial_mul,
        if_neg (by rw [pairIdx_le_iff]; omega)]
    rw [hrem, add_zero]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mem_range] at hq
    rw [elemSym2_pow, MvPowerSeries.coeff_mul_monomial,
      if_pos (pairIdx_le_iff.mpr ⟨by omega, by omega⟩), mul_one, pairIdx_tsub,
      coeff_substS, coeff_bottomSeries, show (i - q) + (j - q) = i + j - 2 * q by omega]
  rw [coeff_subst_elemSymPair, hR]
  exact Finset.sum_congr rfl fun q _ => by rw [coeff_newtonAssembled]

theorem swapInvariant_subst_elemSymPair (g : MvPowerSeries (Fin 2) W) :
    SwapInvariant (MvPowerSeries.subst (elemSymPair (W := W)) g) := by
  rw [swapInvariant_iff_coeff]
  intro i j
  rw [coeff_subst_elemSymPair, coeff_subst_elemSymPair, min_comm j i, Nat.add_comm j i]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.mem_range] at hq
  have hqi : q ≤ i := by omega
  have hqj : q ≤ j := by omega
  have h := Nat.choose_symm (n := i + j - 2 * q) (k := i - q) (by omega)
  rw [show i + j - 2 * q - (i - q) = j - q by omega] at h
  rw [h]

theorem exists_eq_subst_of_swapInvariant {f : MvPowerSeries (Fin 2) W}
    (hf : SwapInvariant f) :
    ∃ g : MvPowerSeries (Fin 2) W, MvPowerSeries.subst elemSymPair g = f :=
  ⟨newtonAssembled f, subst_newtonAssembled hf⟩

theorem swapInvariant_iff_exists_eq_subst (f : MvPowerSeries (Fin 2) W) :
    SwapInvariant f ↔ ∃ g : MvPowerSeries (Fin 2) W,
      MvPowerSeries.subst elemSymPair g = f := by
  constructor
  · exact exists_eq_subst_of_swapInvariant
  · rintro ⟨g, rfl⟩
    exact swapInvariant_subst_elemSymPair g

theorem completed_fundamental_theorem_symmetric_two_vars (f : MvPowerSeries (Fin 2) W)
    (hf : MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) f = f) :
    ∃ g : MvPowerSeries (Fin 2) W,
      f = MvPowerSeries.subst
        ![MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X 1,
          MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X 1] g := by
  obtain ⟨g, hg⟩ := exists_eq_subst_of_swapInvariant (swapInvariant_of hf)
  refine ⟨g, ?_⟩
  rw [show (![MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X 1,
      MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) W)
      = elemSymPair from rfl]
  exact hg.symm

theorem swapInvariant_iff_uvSwapEquiv_eq (f : MvPowerSeries (Fin 2) W) :
    SwapInvariant f ↔ uvSwapEquiv f = f := by
  constructor
  · intro hf
    rw [uvSwapEquiv_apply]
    exact hf.rename_eq
  · intro h
    apply swapInvariant_of
    rw [← uvSwapEquiv_apply]
    exact h

theorem exists_eq_subst_of_uvSwapEquiv_fixed {f : MvPowerSeries (Fin 2) W}
    (hf : uvSwapEquiv f = f) :
    ∃ g : MvPowerSeries (Fin 2) W, MvPowerSeries.subst elemSymPair g = f :=
  exists_eq_subst_of_swapInvariant ((swapInvariant_iff_uvSwapEquiv_eq f).mpr hf)

theorem uvSwapEquiv_fixed_iff_exists_eq_subst (f : MvPowerSeries (Fin 2) W) :
    uvSwapEquiv f = f ↔ ∃ g : MvPowerSeries (Fin 2) W,
      MvPowerSeries.subst elemSymPair g = f := by
  rw [← swapInvariant_iff_uvSwapEquiv_eq]
  exact swapInvariant_iff_exists_eq_subst f

end

end SymmetricTwoVars
p2m_reactivate "P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve.SymmetricTwoVars"

end ModularCurve
p2m_reactivate "P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve.SymmetricTwoVars P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "uvCrossingIdeal UVCrossingModel uvSwapEquiv uvSwapEquiv_apply uvSwapEquiv_X_zero uvSwapEquiv_crossing UVCrossingModel.range_chartHom_le_fixedSubring"
p2m_open "ModularCurve"

noncomputable section

namespace UVCrossingModel
p2m_export "ModularCurve.UVCrossingModel" "sAmbient sAmbient_def chartHom chartHom_apply mk U const mk_surjective crossingSwap crossingSwap_mk fixedSubring mem_fixedSubring_iff chartHom_C range_chartHom_le_fixedSubring U_notMem_fixedSubring"
p2m_open "ModularCurve.UVCrossingModel"

open SymmetricTwoVars

section CrossingGenerator

variable {W : Type u} [CommRing W]

theorem coeff_mul_crossing (π : W) (h : MvPowerSeries (Fin 2) W) (i j : ℕ) :
    MvPowerSeries.coeff (pairIdx i j)
        (h * ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1
          - MvPowerSeries.C π))
      = (if 1 ≤ i ∧ 1 ≤ j then MvPowerSeries.coeff (pairIdx (i - 1) (j - 1)) h else 0)
        - MvPowerSeries.coeff (pairIdx i j) h * π := by
  classical
  have he : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1
      = MvPowerSeries.monomial (pairIdx 1 1) 1 := by
    rw [← elemSym2_def]
    exact elemSym2_eq_monomial
  rw [mul_sub, map_sub, MvPowerSeries.coeff_mul_C, he, MvPowerSeries.coeff_mul_monomial]
  congr 1
  by_cases hij : pairIdx 1 1 ≤ pairIdx i j
  · rw [if_pos hij, if_pos (pairIdx_le_iff.mp hij), pairIdx_tsub, mul_one]
  · rw [if_neg hij, if_neg fun hc => hij (pairIdx_le_iff.mpr hc)]

theorem eq_zero_of_mul_crossing_eq_zero [IsDomain W] {π : W}
    {h : MvPowerSeries (Fin 2) W}
    (hzero : h * ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1
      - MvPowerSeries.C π) = 0) :
    h = 0 := by
  have hrel : ∀ i j : ℕ,
      (if 1 ≤ i ∧ 1 ≤ j then MvPowerSeries.coeff (pairIdx (i - 1) (j - 1)) h else 0)
        = MvPowerSeries.coeff (pairIdx i j) h * π := by
    intro i j
    have h0 : MvPowerSeries.coeff (pairIdx i j)
        (h * ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1
          - MvPowerSeries.C π)) = 0 := by
      rw [hzero, map_zero]
    rw [coeff_mul_crossing] at h0
    exact sub_eq_zero.mp h0
  rcases eq_or_ne π 0 with rfl | hπ
  ·
    apply MvPowerSeries.ext
    intro d
    obtain ⟨i, j, rfl⟩ : ∃ i j, d = pairIdx i j := ⟨d 0, d 1, eq_pairIdx d⟩
    have hr := hrel (i + 1) (j + 1)
    rw [if_pos ⟨by omega, by omega⟩, mul_zero] at hr
    rw [map_zero]
    simpa using hr
  ·
    apply MvPowerSeries.ext
    intro d
    obtain ⟨i, j, rfl⟩ : ∃ i j, d = pairIdx i j := ⟨d 0, d 1, eq_pairIdx d⟩
    rw [map_zero]
    suffices hkey : ∀ m i j : ℕ, min i j ≤ m → MvPowerSeries.coeff (pairIdx i j) h = 0 from
      hkey (min i j) i j le_rfl
    intro m
    induction m with
    | zero =>
      intro i j hm
      have hr := hrel i j
      rw [if_neg (by omega)] at hr
      rcases mul_eq_zero.mp hr.symm with hc | hc
      · exact hc
      · exact absurd hc hπ
    | succ m ih =>
      intro i j hm
      by_cases hij : 1 ≤ i ∧ 1 ≤ j
      · have hr := hrel i j
        rw [if_pos hij, ih (i - 1) (j - 1) (by omega)] at hr
        rcases mul_eq_zero.mp hr.symm with hc | hc
        · exact hc
        · exact absurd hc hπ
      · have hr := hrel i j
        rw [if_neg hij] at hr
        rcases mul_eq_zero.mp hr.symm with hc | hc
        · exact hc
        · exact absurd hc hπ

theorem crossingGen_mem_nonZeroDivisors [IsDomain W] (π : W) :
    ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 - MvPowerSeries.C π)
      ∈ nonZeroDivisors (MvPowerSeries (Fin 2) W) := by
  rw [mem_nonZeroDivisors_iff]
  constructor
  · intro x hx
    exact eq_zero_of_mul_crossing_eq_zero (by rw [mul_comm] at hx; exact hx)
  · intro x hx
    exact eq_zero_of_mul_crossing_eq_zero hx

theorem mk_crossing_eq_zero (π : W) :
    mk π ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1
      - MvPowerSeries.C π) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)

theorem mk_elemSym2 (π : W) :
    mk π (elemSym2 : MvPowerSeries (Fin 2) W) = const π π := by
  show Ideal.Quotient.mk (uvCrossingIdeal W π) _ = Ideal.Quotient.mk (uvCrossingIdeal W π) _
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, elemSym2_def]
  exact Ideal.subset_span rfl

theorem mk_substS (π : W) (φ : PowerSeries W) :
    mk π (substS φ) = chartHom π φ := by
  rw [chartHom_apply, substS_def,
    show (elemSym1 : MvPowerSeries (Fin 2) W) = sAmbient W by
      rw [elemSym1_def, sAmbient_def]]

end CrossingGenerator
p2m_reactivate "P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve.SymmetricTwoVars P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve"

section LowerPart

variable {W : Type u} [CommRing W]

theorem coeff_uvSwapEquiv (f : MvPowerSeries (Fin 2) W) (i j : ℕ) :
    MvPowerSeries.coeff (pairIdx i j) (uvSwapEquiv f)
      = MvPowerSeries.coeff (pairIdx j i) f := by
  rw [uvSwapEquiv_apply, coeff_rename_swap, mapDomain_swap_pairIdx]

def lowerPart (g : MvPowerSeries (Fin 2) W) : MvPowerSeries (Fin 2) W :=
  fun d => if d 1 < d 0 then MvPowerSeries.coeff d g else 0

theorem coeff_lowerPart' (g : MvPowerSeries (Fin 2) W) (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (lowerPart g)
      = if d 1 < d 0 then MvPowerSeries.coeff d g else 0 := rfl

theorem coeff_lowerPart (g : MvPowerSeries (Fin 2) W) (i j : ℕ) :
    MvPowerSeries.coeff (pairIdx i j) (lowerPart g)
      = if j < i then MvPowerSeries.coeff (pairIdx i j) g else 0 := by
  rw [coeff_lowerPart', pairIdx_apply_zero, pairIdx_apply_one]

theorem coeff_diag_eq_zero_of_anti (htwo : ∀ w : W, w + w = 0 → w = 0)
    {g : MvPowerSeries (Fin 2) W} (hanti : uvSwapEquiv g = -g) (i : ℕ) :
    MvPowerSeries.coeff (pairIdx i i) g = 0 := by
  have h6 : MvPowerSeries.coeff (pairIdx i i) (uvSwapEquiv g)
      = MvPowerSeries.coeff (pairIdx i i) g := coeff_uvSwapEquiv g i i
  rw [hanti, map_neg] at h6
  have h7 : MvPowerSeries.coeff (pairIdx i i) g
      = -MvPowerSeries.coeff (pairIdx i i) g := h6.symm
  rw [eq_neg_iff_add_eq_zero] at h7
  exact htwo _ h7

theorem lowerPart_sub_uvSwapEquiv {g : MvPowerSeries (Fin 2) W}
    (hanti : uvSwapEquiv g = -g)
    (hdiag : ∀ i : ℕ, MvPowerSeries.coeff (pairIdx i i) g = 0) :
    lowerPart g - uvSwapEquiv (lowerPart g) = g := by
  apply MvPowerSeries.ext
  intro d
  obtain ⟨i, j, rfl⟩ : ∃ i j, d = pairIdx i j := ⟨d 0, d 1, eq_pairIdx d⟩
  rw [map_sub, coeff_uvSwapEquiv, coeff_lowerPart, coeff_lowerPart]
  have hg : MvPowerSeries.coeff (pairIdx j i) g
      = -MvPowerSeries.coeff (pairIdx i j) g := by
    have h8 := coeff_uvSwapEquiv g i j
    rw [hanti, map_neg] at h8
    exact h8.symm
  rcases lt_trichotomy j i with hlt | heq | hgt
  · rw [if_pos hlt, if_neg (by omega), sub_zero]
  · rw [if_neg (by omega), if_neg (by omega), sub_zero]
    have h9 : MvPowerSeries.coeff (pairIdx i j) g = 0 := by
      rw [heq]
      exact hdiag i
    exact h9.symm
  · rw [if_neg (by omega), if_pos hgt, zero_sub, hg, neg_neg]

end LowerPart
p2m_reactivate "P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve.SymmetricTwoVars P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve"

section SymmetricLift

variable {W : Type u} [CommRing W]

theorem exists_uvSwapEquiv_fixed_lift {π : W}
    (hreg : ∀ h : MvPowerSeries (Fin 2) W,
      h * ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1
        - MvPowerSeries.C π) = 0 → h = 0)
    (htwo : ∀ w : W, w + w = 0 → w = 0)
    {x : UVCrossingModel W π} (hx : x ∈ fixedSubring π) :
    ∃ F : MvPowerSeries (Fin 2) W, uvSwapEquiv F = F ∧ mk π F = x := by
  obtain ⟨F₀, hF₀⟩ := mk_surjective π x
  have h1 : mk π (uvSwapEquiv F₀) = mk π F₀ := by
    have hswap := mem_fixedSubring_iff.mp hx
    calc mk π (uvSwapEquiv F₀) = crossingSwap π (mk π F₀) := (crossingSwap_mk π F₀).symm
      _ = crossingSwap π x := by rw [hF₀]
      _ = x := hswap
      _ = mk π F₀ := hF₀.symm
  have h2 : uvSwapEquiv F₀ - F₀ ∈ uvCrossingIdeal W π := by
    rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact h1
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp h2

  have hanti : uvSwapEquiv g = -g := by
    have h3 : uvSwapEquiv (W := W)
        (g * ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1
          - MvPowerSeries.C π))
        = uvSwapEquiv (uvSwapEquiv F₀ - F₀) := by rw [hg]
    rw [map_mul, uvSwapEquiv_crossing, map_sub, uvSwapEquiv_uvSwapEquiv] at h3
    have h4 : (uvSwapEquiv g + g)
        * ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1
          - MvPowerSeries.C π) = 0 := by
      rw [add_mul, h3, hg]
      ring
    exact eq_neg_of_add_eq_zero_left (hreg _ h4)
  have hdiag := coeff_diag_eq_zero_of_anti htwo hanti
  have hsplit := lowerPart_sub_uvSwapEquiv hanti hdiag
  refine ⟨F₀ + lowerPart g
    * ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1
      - MvPowerSeries.C π), ?_, ?_⟩
  · have h8 : uvSwapEquiv F₀ = F₀ + g
        * ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1
          - MvPowerSeries.C π) := by
      rw [hg]
      ring
    set lp := lowerPart g with hlp
    rw [map_add, map_mul, uvSwapEquiv_crossing, h8, ← hsplit]
    ring
  · rw [map_add, map_mul, mk_crossing_eq_zero, mul_zero, add_zero, hF₀]

end SymmetricLift
p2m_reactivate "P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve.SymmetricTwoVars P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve"

section ChartPartial

variable {W : Type u} [CommRing W]

def chartPartial (π : W) (F : MvPowerSeries (Fin 2) W) (B : ℕ) : PowerSeries W :=
  ∑ q ∈ Finset.range B, PowerSeries.C (π ^ q) * bottomSeries (newton F q)

theorem chartPartial_def (π : W) (F : MvPowerSeries (Fin 2) W) (B : ℕ) :
    chartPartial π F B
      = ∑ q ∈ Finset.range B, PowerSeries.C (π ^ q) * bottomSeries (newton F q) := rfl

theorem coeff_chartPartial (π : W) (F : MvPowerSeries (Fin 2) W) (B n : ℕ) :
    PowerSeries.coeff n (chartPartial π F B)
      = ∑ q ∈ Finset.range B, π ^ q * MvPowerSeries.coeff (pairIdx n 0) (newton F q) := by
  rw [chartPartial_def, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [PowerSeries.coeff_C_mul, coeff_bottomSeries]

theorem chartHom_chartPartial (π : W) (F : MvPowerSeries (Fin 2) W) (B : ℕ) :
    chartHom π (chartPartial π F B)
      = ∑ q ∈ Finset.range B, const π π ^ q * chartHom π (bottomSeries (newton F q)) := by
  rw [chartPartial_def, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_mul, chartHom_C, const_pow]

theorem mk_eq_chartHom_chartPartial_add (π : W) {F : MvPowerSeries (Fin 2) W}
    (hF : SwapInvariant F) (B : ℕ) :
    mk π F = chartHom π (chartPartial π F B) + const π π ^ B * mk π (newton F B) := by
  conv_lhs => rw [newton_telescope hF B]
  rw [map_add, map_sum, map_mul, map_pow, mk_elemSym2, chartHom_chartPartial]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_mul, map_pow, mk_elemSym2, mk_substS, mul_comm]

end ChartPartial
p2m_reactivate "P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve.SymmetricTwoVars P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve"

section AdicLimit

variable {W : Type u} [CommRing W]

theorem exists_eq_C_mul_of_forall_dvd (c : W) (φ : PowerSeries W)
    (h : ∀ n : ℕ, c ∣ PowerSeries.coeff n φ) :
    ∃ ψ : PowerSeries W, φ = PowerSeries.C c * ψ := by
  choose ψc hψc using h
  refine ⟨PowerSeries.mk ψc, PowerSeries.ext fun n => ?_⟩
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
  exact hψc n

theorem exists_chartLimit (π : W) [IsPrecomplete (Ideal.span {π}) W]
    (F : MvPowerSeries (Fin 2) W) :
    ∃ f : PowerSeries W, ∀ B n : ℕ,
      π ^ B ∣ PowerSeries.coeff n (f - chartPartial π F B) := by
  have hcauchy : ∀ n : ℕ, ∀ {B B' : ℕ}, B ≤ B' →
      PowerSeries.coeff n (chartPartial π F B) ≡ PowerSeries.coeff n (chartPartial π F B')
        [SMOD (Ideal.span {π} ^ B • ⊤ : Submodule W W)] := by
    intro n B B' hBB'
    rw [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    have hsplit : PowerSeries.coeff n (chartPartial π F B')
        = PowerSeries.coeff n (chartPartial π F B)
          + ∑ q ∈ Finset.Ico B B',
              π ^ q * MvPowerSeries.coeff (pairIdx n 0) (newton F q) := by
      rw [coeff_chartPartial π F B' n, coeff_chartPartial π F B n]
      exact (Finset.sum_range_add_sum_Ico _ hBB').symm
    rw [hsplit, sub_add_cancel_left]
    exact dvd_neg.mpr (Finset.dvd_sum fun q hq =>
      dvd_mul_of_dvd_left (pow_dvd_pow π (Finset.mem_Ico.mp hq).1) _)
  have hex : ∀ n : ℕ, ∃ L : W, ∀ B : ℕ,
      PowerSeries.coeff n (chartPartial π F B) ≡ L
        [SMOD (Ideal.span {π} ^ B • ⊤ : Submodule W W)] :=
    fun n => IsPrecomplete.prec inferInstance (hcauchy n)
  choose L hL using hex
  refine ⟨PowerSeries.mk L, fun B n => ?_⟩
  have h1 := hL n B
  rw [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at h1
  rw [map_sub, PowerSeries.coeff_mk, ← neg_sub]
  exact dvd_neg.mpr h1

end AdicLimit
p2m_reactivate "P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve.SymmetricTwoVars P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve"

section Surjectivity

variable {W : Type u} [CommRing W]

theorem mk_mem_range_chartHom_of_uvSwapEquiv_fixed {π : W}
    [IsPrecomplete (Ideal.span {π}) W]
    (hsep : ∀ x : UVCrossingModel W π,
      (∀ B : ℕ, x ∈ Ideal.span {const π π} ^ B) → x = 0)
    {F : MvPowerSeries (Fin 2) W} (hF : uvSwapEquiv F = F) :
    mk π F ∈ Set.range (chartHom π) := by
  have hF' : SwapInvariant F := (swapInvariant_iff_uvSwapEquiv_eq F).mpr hF
  obtain ⟨f, hf⟩ := exists_chartLimit π F
  refine ⟨f, ?_⟩
  have hzero : chartHom π f - mk π F = 0 := by
    apply hsep
    intro B
    obtain ⟨ψ, hψ⟩ := exists_eq_C_mul_of_forall_dvd (π ^ B) (f - chartPartial π F B) (hf B)
    have h2 : chartHom π (f - chartPartial π F B) = const π π ^ B * chartHom π ψ := by
      rw [hψ, map_mul, chartHom_C, const_pow]
    have h3 := mk_eq_chartHom_chartPartial_add π hF' B
    have hkey : chartHom π f - mk π F
        = const π π ^ B * (chartHom π ψ - mk π (newton F B)) := by
      calc chartHom π f - mk π F
          = chartHom π (f - chartPartial π F B)
              - (mk π F - chartHom π (chartPartial π F B)) := by
            rw [map_sub]
            ring
        _ = const π π ^ B * chartHom π ψ
              - (chartHom π (chartPartial π F B) + const π π ^ B * mk π (newton F B)
                  - chartHom π (chartPartial π F B)) := by rw [h2, h3]
        _ = const π π ^ B * (chartHom π ψ - mk π (newton F B)) := by ring
    rw [hkey, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton'.mpr ⟨_, mul_comm _ _⟩
  exact sub_eq_zero.mp hzero

theorem chartHom_surjOn_fixedSubring {π : W} [IsPrecomplete (Ideal.span {π}) W]
    (hreg : ∀ h : MvPowerSeries (Fin 2) W,
      h * ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1
        - MvPowerSeries.C π) = 0 → h = 0)
    (htwo : ∀ w : W, w + w = 0 → w = 0)
    (hsep : ∀ x : UVCrossingModel W π,
      (∀ B : ℕ, x ∈ Ideal.span {const π π} ^ B) → x = 0) :
    ∀ x ∈ fixedSubring π, x ∈ Set.range (chartHom π) := by
  intro x hx
  obtain ⟨F, hFsym, hFmk⟩ := exists_uvSwapEquiv_fixed_lift hreg htwo hx
  rw [← hFmk]
  exact mk_mem_range_chartHom_of_uvSwapEquiv_fixed hsep hFsym

theorem fixedSubring_le_range_chartHom {π : W} [IsPrecomplete (Ideal.span {π}) W]
    (hreg : ∀ h : MvPowerSeries (Fin 2) W,
      h * ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1
        - MvPowerSeries.C π) = 0 → h = 0)
    (htwo : ∀ w : W, w + w = 0 → w = 0)
    (hsep : ∀ x : UVCrossingModel W π,
      (∀ B : ℕ, x ∈ Ideal.span {const π π} ^ B) → x = 0) :
    fixedSubring π ≤ (chartHom π).range := by
  intro x hx
  obtain ⟨f, hf⟩ := chartHom_surjOn_fixedSubring hreg htwo hsep x hx
  exact RingHom.mem_range.mpr ⟨f, hf⟩

theorem range_chartHom_eq_fixedSubring' {π : W} [IsPrecomplete (Ideal.span {π}) W]
    (hreg : ∀ h : MvPowerSeries (Fin 2) W,
      h * ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1
        - MvPowerSeries.C π) = 0 → h = 0)
    (htwo : ∀ w : W, w + w = 0 → w = 0)
    (hsep : ∀ x : UVCrossingModel W π,
      (∀ B : ℕ, x ∈ Ideal.span {const π π} ^ B) → x = 0) :
    (chartHom π).range = fixedSubring π :=
  le_antisymm (range_chartHom_le_fixedSubring π)
    (fixedSubring_le_range_chartHom hreg htwo hsep)

theorem not_isUnit_const_self {π : W} (hπ : ¬IsUnit π) : ¬IsUnit (const π π) := by
  intro hu
  apply hπ
  obtain ⟨z, hz⟩ := hu.exists_right_inv
  obtain ⟨Z, rfl⟩ := mk_surjective π z
  have h1 : mk π (MvPowerSeries.C π * Z - 1) = 0 := by
    rw [map_sub, map_mul, map_one,
      show mk π (MvPowerSeries.C π) = const π π from rfl, hz, sub_self]
  have h2 : MvPowerSeries.C π * Z - 1 ∈ uvCrossingIdeal W π :=
    Ideal.Quotient.eq_zero_iff_mem.mp h1
  obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.mp h2
  have hcc : MvPowerSeries.constantCoeff (σ := Fin 2) (R := W)
      (h * ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1
        - MvPowerSeries.C π))
      = MvPowerSeries.constantCoeff (σ := Fin 2) (R := W)
        (MvPowerSeries.C π * Z - 1) := by rw [hh]
  simp only [map_mul, map_sub, map_one, MvPowerSeries.constantCoeff_X,
    MvPowerSeries.constantCoeff_C, mul_zero, zero_sub, mul_neg] at hcc
  refine IsUnit.of_mul_eq_one
    (MvPowerSeries.constantCoeff Z + MvPowerSeries.constantCoeff h) ?_
  linear_combination -hcc

end Surjectivity
p2m_reactivate "P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve.SymmetricTwoVars P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve"

section NoTwo

variable {W : Type u} [CommRing W]

open SymmetricTwoVars

def diagPart (g : MvPowerSeries (Fin 2) W) : MvPowerSeries (Fin 2) W :=
  fun d => if d 0 = d 1 then MvPowerSeries.coeff d g else 0

theorem coeff_diagPart' (g : MvPowerSeries (Fin 2) W) (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (diagPart g) = if d 0 = d 1 then MvPowerSeries.coeff d g else 0 := rfl

theorem coeff_diagPart (g : MvPowerSeries (Fin 2) W) (i j : ℕ) :
    MvPowerSeries.coeff (pairIdx i j) (diagPart g)
      = if i = j then MvPowerSeries.coeff (pairIdx i j) g else 0 := by
  rw [coeff_diagPart', pairIdx_apply_zero, pairIdx_apply_one]

theorem coeff_diag_eq_zero_of_hreg {π : W}
    (hreg : ∀ h : MvPowerSeries (Fin 2) W,
      h * ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1
        - MvPowerSeries.C π) = 0 → h = 0)
    {g F₀ : MvPowerSeries (Fin 2) W}
    (hg : g * ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1
        - MvPowerSeries.C π) = uvSwapEquiv F₀ - F₀) (i : ℕ) :
    MvPowerSeries.coeff (pairIdx i i) g = 0 := by
  have hA : ∀ n : ℕ, MvPowerSeries.coeff (pairIdx n n)
      (g * ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1
        - MvPowerSeries.C π)) = 0 := by
    intro n
    rw [hg, map_sub, coeff_uvSwapEquiv, sub_self]
  have hD : diagPart g * ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1
      - MvPowerSeries.C π) = 0 := by
    apply MvPowerSeries.ext
    intro d
    obtain ⟨a, b, rfl⟩ : ∃ a b, d = pairIdx a b := ⟨d 0, d 1, eq_pairIdx d⟩
    rw [map_zero, coeff_mul_crossing]
    by_cases hab : a = b
    · subst hab
      have hAa := hA a
      rw [coeff_mul_crossing] at hAa
      rw [coeff_diagPart g a a, if_pos rfl]
      by_cases h1 : 1 ≤ a ∧ 1 ≤ a
      · rw [if_pos h1, coeff_diagPart, if_pos rfl]
        rw [if_pos h1] at hAa
        exact hAa
      · rw [if_neg h1]
        rw [if_neg h1] at hAa
        exact hAa
    · rw [coeff_diagPart g a b, if_neg hab, zero_mul, sub_zero]
      by_cases h1 : 1 ≤ a ∧ 1 ≤ b
      · rw [if_pos h1, coeff_diagPart, if_neg (by omega)]
      · rw [if_neg h1]
  have hz := congrArg (MvPowerSeries.coeff (pairIdx i i)) (hreg _ hD)
  rw [coeff_diagPart, if_pos rfl, map_zero] at hz
  exact hz

theorem exists_uvSwapEquiv_fixed_lift_noTwo {π : W}
    (hreg : ∀ h : MvPowerSeries (Fin 2) W,
      h * ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1
        - MvPowerSeries.C π) = 0 → h = 0)
    {x : UVCrossingModel W π} (hx : x ∈ fixedSubring π) :
    ∃ F : MvPowerSeries (Fin 2) W, uvSwapEquiv F = F ∧ mk π F = x := by
  obtain ⟨F₀, hF₀⟩ := mk_surjective π x
  have h1 : mk π (uvSwapEquiv F₀) = mk π F₀ := by
    have hswap := mem_fixedSubring_iff.mp hx
    calc mk π (uvSwapEquiv F₀) = crossingSwap π (mk π F₀) := (crossingSwap_mk π F₀).symm
      _ = crossingSwap π x := by rw [hF₀]
      _ = x := hswap
      _ = mk π F₀ := hF₀.symm
  have h2 : uvSwapEquiv F₀ - F₀ ∈ uvCrossingIdeal W π := by
    rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact h1
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp h2

  have hanti : uvSwapEquiv g = -g := by
    have h3 : uvSwapEquiv (W := W)
        (g * ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1
          - MvPowerSeries.C π))
        = uvSwapEquiv (uvSwapEquiv F₀ - F₀) := by rw [hg]
    rw [map_mul, uvSwapEquiv_crossing, map_sub, uvSwapEquiv_uvSwapEquiv] at h3
    have h4 : (uvSwapEquiv g + g)
        * ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1
          - MvPowerSeries.C π) = 0 := by
      rw [add_mul, h3, hg]
      ring
    exact eq_neg_of_add_eq_zero_left (hreg _ h4)
  have hdiag : ∀ i : ℕ, MvPowerSeries.coeff (pairIdx i i) g = 0 :=
    fun i => coeff_diag_eq_zero_of_hreg hreg hg i
  have hsplit := lowerPart_sub_uvSwapEquiv hanti hdiag
  refine ⟨F₀ + lowerPart g
    * ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1
      - MvPowerSeries.C π), ?_, ?_⟩
  · have h8 : uvSwapEquiv F₀ = F₀ + g
        * ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1
          - MvPowerSeries.C π) := by
      rw [hg]
      ring
    set lp := lowerPart g with hlp
    rw [map_add, map_mul, uvSwapEquiv_crossing, h8, ← hsplit]
    ring
  · rw [map_add, map_mul, mk_crossing_eq_zero, mul_zero, add_zero, hF₀]

theorem chartHom_surjOn_fixedSubring_noTwo {π : W} [IsPrecomplete (Ideal.span {π}) W]
    (hreg : ∀ h : MvPowerSeries (Fin 2) W,
      h * ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1
        - MvPowerSeries.C π) = 0 → h = 0)
    (hsep : ∀ x : UVCrossingModel W π,
      (∀ B : ℕ, x ∈ Ideal.span {const π π} ^ B) → x = 0) :
    ∀ x ∈ fixedSubring π, x ∈ Set.range (chartHom π) := by
  intro x hx
  obtain ⟨F, hFsym, hFmk⟩ := exists_uvSwapEquiv_fixed_lift_noTwo hreg hx
  rw [← hFmk]
  exact mk_mem_range_chartHom_of_uvSwapEquiv_fixed hsep hFsym

theorem range_chartHom_eq_fixedSubring_noTwo {π : W} [IsPrecomplete (Ideal.span {π}) W]
    (hreg : ∀ h : MvPowerSeries (Fin 2) W,
      h * ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1
        - MvPowerSeries.C π) = 0 → h = 0)
    (hsep : ∀ x : UVCrossingModel W π,
      (∀ B : ℕ, x ∈ Ideal.span {const π π} ^ B) → x = 0) :
    (chartHom π).range = fixedSubring π :=
  le_antisymm (ModularCurve.UVCrossingModel.range_chartHom_le_fixedSubring π) (by
    intro x hx
    obtain ⟨f, hf⟩ := chartHom_surjOn_fixedSubring_noTwo hreg hsep x hx
    exact ⟨f, hf⟩)

end NoTwo
p2m_reactivate "P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve.SymmetricTwoVars P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve"

end UVCrossingModel
p2m_reactivate "P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve.SymmetricTwoVars P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve"

end
p2m_reactivate "P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve.SymmetricTwoVars P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve"

end ModularCurve
p2m_reactivate "P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve.SymmetricTwoVars P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve"

end
p2m_reactivate "P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve.SymmetricTwoVars P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "uvCrossingIdeal UVCrossingModel uvSwapEquiv uvSwapEquiv_apply uvSwapEquiv_X_zero uvSwapEquiv_crossing UVCrossingModel.range_chartHom_le_fixedSubring"
p2m_open "ModularCurve"

noncomputable section

namespace UVCrossingModel
p2m_export "ModularCurve.UVCrossingModel" "sAmbient sAmbient_def chartHom chartHom_apply mk U const mk_surjective crossingSwap crossingSwap_mk fixedSubring mem_fixedSubring_iff chartHom_C range_chartHom_le_fixedSubring U_notMem_fixedSubring"
p2m_open "ModularCurve.UVCrossingModel"

open SymmetricTwoVars

theorem algebraMap_fixedSubring_eq_subtype {W : Type u} [CommRing W] (π : W) :
    algebraMap (fixedSubring π) (UVCrossingModel W π) = (fixedSubring π).subtype :=
  rfl

section CoeffMulX

variable {W : Type u} [CommRing W]

theorem pairIdx_one_zero : pairIdx 1 0 = Finsupp.single (0 : Fin 2) 1 := by
  rw [pairIdx_def, Finsupp.single_zero, add_zero]

theorem pairIdx_zero_one : pairIdx 0 1 = Finsupp.single (1 : Fin 2) 1 := by
  rw [pairIdx_def, Finsupp.single_zero, zero_add]

theorem X_zero_eq_monomial :
    (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) W)
      = MvPowerSeries.monomial (pairIdx 1 0) 1 := by
  rw [MvPowerSeries.X_def, pairIdx_one_zero]

theorem X_one_eq_monomial :
    (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) W)
      = MvPowerSeries.monomial (pairIdx 0 1) 1 := by
  rw [MvPowerSeries.X_def, pairIdx_zero_one]

theorem coeff_mul_X_zero (h : MvPowerSeries (Fin 2) W) (i j : ℕ) :
    MvPowerSeries.coeff (pairIdx i j) (h * MvPowerSeries.X 0)
      = if 1 ≤ i then MvPowerSeries.coeff (pairIdx (i - 1) j) h else 0 := by
  rw [X_zero_eq_monomial, MvPowerSeries.coeff_mul_monomial]
  by_cases hle : pairIdx 1 0 ≤ pairIdx i j
  · rw [if_pos hle, if_pos (pairIdx_le_iff.mp hle).1, pairIdx_tsub, Nat.sub_zero, mul_one]
  · rw [if_neg hle, if_neg fun hc => hle (pairIdx_le_iff.mpr ⟨hc, Nat.zero_le j⟩)]

theorem coeff_mul_X_one (h : MvPowerSeries (Fin 2) W) (i j : ℕ) :
    MvPowerSeries.coeff (pairIdx i j) (h * MvPowerSeries.X 1)
      = if 1 ≤ j then MvPowerSeries.coeff (pairIdx i (j - 1)) h else 0 := by
  rw [X_one_eq_monomial, MvPowerSeries.coeff_mul_monomial]
  by_cases hle : pairIdx 0 1 ≤ pairIdx i j
  · rw [if_pos hle, if_pos (pairIdx_le_iff.mp hle).2, pairIdx_tsub, Nat.sub_zero, mul_one]
  · rw [if_neg hle, if_neg fun hc => hle (pairIdx_le_iff.mpr ⟨Nat.zero_le i, hc⟩)]

theorem coeff_mul_X_zero_sub_X_one (h : MvPowerSeries (Fin 2) W) (i j : ℕ) :
    MvPowerSeries.coeff (pairIdx i j)
        (h * (MvPowerSeries.X 0 - MvPowerSeries.X 1))
      = (if 1 ≤ i then MvPowerSeries.coeff (pairIdx (i - 1) j) h else 0)
        - (if 1 ≤ j then MvPowerSeries.coeff (pairIdx i (j - 1)) h else 0) := by
  rw [mul_sub, map_sub, coeff_mul_X_zero, coeff_mul_X_one]

end CoeffMulX
p2m_reactivate "P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve.SymmetricTwoVars P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve"

section AntiDiagSolve

variable {W : Type u} [CommRing W]

def antiDiagSolve (g : MvPowerSeries (Fin 2) W) : MvPowerSeries (Fin 2) W :=
  fun d => ∑ t ∈ Finset.range (d 1 + 1),
    MvPowerSeries.coeff (pairIdx (d 0 + 1 + t) (d 1 - t)) g

theorem coeff_antiDiagSolve (g : MvPowerSeries (Fin 2) W) (i j : ℕ) :
    MvPowerSeries.coeff (pairIdx i j) (antiDiagSolve g)
      = ∑ t ∈ Finset.range (j + 1),
          MvPowerSeries.coeff (pairIdx (i + 1 + t) (j - t)) g := by
  have h : MvPowerSeries.coeff (pairIdx i j) (antiDiagSolve g)
      = ∑ t ∈ Finset.range ((pairIdx i j) 1 + 1),
          MvPowerSeries.coeff
            (pairIdx ((pairIdx i j) 0 + 1 + t) ((pairIdx i j) 1 - t)) g := rfl
  rw [h]
  simp only [pairIdx_apply_zero, pairIdx_apply_one]

end AntiDiagSolve
p2m_reactivate "P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve.SymmetricTwoVars P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve"

section AntiInvariant

variable {W : Type u} [CommRing W]

theorem coeff_swap_eq_neg_of_anti {g : MvPowerSeries (Fin 2) W}
    (hanti : uvSwapEquiv g = -g) (i j : ℕ) :
    MvPowerSeries.coeff (pairIdx j i) g = -MvPowerSeries.coeff (pairIdx i j) g := by
  have h := coeff_uvSwapEquiv g i j
  rw [hanti, map_neg] at h
  exact h.symm

theorem sum_antidiagonal_coeff_eq_zero {g : MvPowerSeries (Fin 2) W}
    (hanti : uvSwapEquiv g = -g)
    (hdiag : ∀ i : ℕ, MvPowerSeries.coeff (pairIdx i i) g = 0) (n : ℕ) :
    ∑ a ∈ Finset.range (n + 1), MvPowerSeries.coeff (pairIdx a (n - a)) g = 0 := by
  refine Finset.sum_involution (fun a _ => n - a) ?_ ?_ ?_ ?_
  · intro a ha
    have haa : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    rw [Nat.sub_sub_self haa, coeff_swap_eq_neg_of_anti hanti a (n - a)]
    exact add_neg_cancel _
  · intro a _ hne heq
    have heq' : n - a = a := heq
    exact hne (by rw [heq']; exact hdiag a)
  · intro a _
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le n a))
  · intro a ha
    exact Nat.sub_sub_self (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha))

end AntiInvariant
p2m_reactivate "P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve.SymmetricTwoVars P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve"

section Division

variable {W : Type u} [CommRing W]

theorem antiDiagSolve_mul_X_zero_sub_X_one {g : MvPowerSeries (Fin 2) W}
    (hanti : uvSwapEquiv g = -g)
    (hdiag : ∀ i : ℕ, MvPowerSeries.coeff (pairIdx i i) g = 0) :
    antiDiagSolve g * (MvPowerSeries.X 0 - MvPowerSeries.X 1) = g := by
  apply MvPowerSeries.ext
  intro d
  obtain ⟨i, j, rfl⟩ : ∃ i j, d = pairIdx i j := ⟨d 0, d 1, eq_pairIdx d⟩
  rw [coeff_mul_X_zero_sub_X_one]
  by_cases hi : 1 ≤ i
  · by_cases hj : 1 ≤ j
    · rw [if_pos hi, if_pos hj, coeff_antiDiagSolve, coeff_antiDiagSolve]
      have h1 : ∑ t ∈ Finset.range (j + 1),
            MvPowerSeries.coeff (pairIdx (i - 1 + 1 + t) (j - t)) g
          = (∑ t ∈ Finset.range j,
              MvPowerSeries.coeff (pairIdx (i + 1 + t) (j - 1 - t)) g)
            + MvPowerSeries.coeff (pairIdx i j) g := by
        calc ∑ t ∈ Finset.range (j + 1),
              MvPowerSeries.coeff (pairIdx (i - 1 + 1 + t) (j - t)) g
            = ∑ t ∈ Finset.range (j + 1),
                MvPowerSeries.coeff (pairIdx (i + t) (j - t)) g :=
              Finset.sum_congr rfl fun t _ => by rw [show i - 1 + 1 + t = i + t by omega]
          _ = (∑ t ∈ Finset.range j,
                MvPowerSeries.coeff (pairIdx (i + (t + 1)) (j - (t + 1))) g)
              + MvPowerSeries.coeff (pairIdx (i + 0) (j - 0)) g :=
              Finset.sum_range_succ' _ j
          _ = (∑ t ∈ Finset.range j,
                MvPowerSeries.coeff (pairIdx (i + 1 + t) (j - 1 - t)) g)
              + MvPowerSeries.coeff (pairIdx i j) g := by
              rw [Nat.add_zero, Nat.sub_zero]
              congr 1
              refine Finset.sum_congr rfl fun t _ => ?_
              rw [show i + (t + 1) = i + 1 + t by omega,
                show j - (t + 1) = j - 1 - t by omega]
      have h2 : ∑ t ∈ Finset.range (j - 1 + 1),
            MvPowerSeries.coeff (pairIdx (i + 1 + t) (j - 1 - t)) g
          = ∑ t ∈ Finset.range j,
              MvPowerSeries.coeff (pairIdx (i + 1 + t) (j - 1 - t)) g := by
        rw [show j - 1 + 1 = j by omega]
      rw [h1, h2, add_sub_cancel_left]
    ·
      rw [if_pos hi, if_neg hj, sub_zero, coeff_antiDiagSolve]
      obtain rfl : j = 0 := by omega
      rw [Finset.sum_range_one, show i - 1 + 1 + 0 = i by omega, Nat.sub_zero]
  · by_cases hj : 1 ≤ j
    ·
      rw [if_neg hi, if_pos hj, zero_sub, coeff_antiDiagSolve]
      obtain rfl : i = 0 := by omega
      have hA := sum_antidiagonal_coeff_eq_zero hanti hdiag j
      rw [Finset.sum_range_succ'] at hA
      rw [Nat.sub_zero] at hA
      have hsum : ∑ t ∈ Finset.range (j - 1 + 1),
            MvPowerSeries.coeff (pairIdx (0 + 1 + t) (j - 1 - t)) g
          = ∑ t ∈ Finset.range j,
              MvPowerSeries.coeff (pairIdx (t + 1) (j - (t + 1))) g := by
        rw [show j - 1 + 1 = j by omega]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [show 0 + 1 + t = t + 1 by omega, show j - 1 - t = j - (t + 1) by omega]
      rw [hsum]
      exact neg_eq_of_add_eq_zero_right hA
    ·
      rw [if_neg hi, if_neg hj, sub_zero]
      obtain rfl : i = 0 := by omega
      obtain rfl : j = 0 := by omega
      exact (hdiag 0).symm

end Division
p2m_reactivate "P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve.SymmetricTwoVars P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve"

section SolverInvariance

variable {W : Type u} [CommRing W]

theorem uvSwapEquiv_antiDiagSolve {g : MvPowerSeries (Fin 2) W}
    (hanti : uvSwapEquiv g = -g)
    (hdiag : ∀ i : ℕ, MvPowerSeries.coeff (pairIdx i i) g = 0) :
    uvSwapEquiv (antiDiagSolve g) = antiDiagSolve g := by
  apply MvPowerSeries.ext
  intro d
  obtain ⟨i, j, rfl⟩ : ∃ i j, d = pairIdx i j := ⟨d 0, d 1, eq_pairIdx d⟩
  rw [coeff_uvSwapEquiv, coeff_antiDiagSolve, coeff_antiDiagSolve]

  have hA := sum_antidiagonal_coeff_eq_zero hanti hdiag (i + j + 1)

  have hsplit : ∑ a ∈ Finset.range (i + j + 1 + 1),
        MvPowerSeries.coeff (pairIdx a (i + j + 1 - a)) g
      = (∑ a ∈ Finset.range (i + 1),
          MvPowerSeries.coeff (pairIdx a (i + j + 1 - a)) g)
        + ∑ t ∈ Finset.range (j + 1),
            MvPowerSeries.coeff (pairIdx (i + 1 + t) (i + j + 1 - (i + 1 + t))) g := by
    rw [show i + j + 1 + 1 = (i + 1) + (j + 1) by omega]
    exact Finset.sum_range_add _ (i + 1) (j + 1)

  have htail : ∑ t ∈ Finset.range (j + 1),
        MvPowerSeries.coeff (pairIdx (i + 1 + t) (i + j + 1 - (i + 1 + t))) g
      = ∑ t ∈ Finset.range (j + 1),
          MvPowerSeries.coeff (pairIdx (i + 1 + t) (j - t)) g :=
    Finset.sum_congr rfl fun t _ => by rw [show i + j + 1 - (i + 1 + t) = j - t by omega]

  have hhead : ∑ a ∈ Finset.range (i + 1),
        MvPowerSeries.coeff (pairIdx a (i + j + 1 - a)) g
      = -∑ t ∈ Finset.range (i + 1),
          MvPowerSeries.coeff (pairIdx (j + 1 + t) (i - t)) g := by
    have hterm : ∀ a, MvPowerSeries.coeff (pairIdx a (i + j + 1 - a)) g
        = -MvPowerSeries.coeff (pairIdx (i + j + 1 - a) a) g := fun a =>
      coeff_swap_eq_neg_of_anti hanti (i + j + 1 - a) a
    calc ∑ a ∈ Finset.range (i + 1),
          MvPowerSeries.coeff (pairIdx a (i + j + 1 - a)) g
        = ∑ a ∈ Finset.range (i + 1),
            -MvPowerSeries.coeff (pairIdx (i + j + 1 - a) a) g :=
          Finset.sum_congr rfl fun a _ => hterm a
      _ = -∑ a ∈ Finset.range (i + 1),
            MvPowerSeries.coeff (pairIdx (i + j + 1 - a) a) g := by
          rw [Finset.sum_neg_distrib]
      _ = -∑ t ∈ Finset.range (i + 1),
            MvPowerSeries.coeff (pairIdx (j + 1 + t) (i - t)) g := by
          congr 1
          rw [← Finset.sum_range_reflect
            (fun t => MvPowerSeries.coeff (pairIdx (i + j + 1 - t) t) g) (i + 1)]
          refine Finset.sum_congr rfl fun t ht => ?_
          have ht' : t ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
          rw [show i + 1 - 1 - t = i - t by omega,
            show i + j + 1 - (i - t) = j + 1 + t by omega]

  rw [hsplit, htail, hhead] at hA
  exact neg_add_eq_zero.mp hA

end SolverInvariance
p2m_reactivate "P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve.SymmetricTwoVars P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve"

section Decomposition

variable {W : Type u} [CommRing W]

theorem uvSwapEquiv_sub_uvSwapEquiv (f : MvPowerSeries (Fin 2) W) :
    uvSwapEquiv (f - uvSwapEquiv f) = -(f - uvSwapEquiv f) := by
  rw [map_sub, uvSwapEquiv_uvSwapEquiv, neg_sub]

theorem coeff_diag_sub_uvSwapEquiv (f : MvPowerSeries (Fin 2) W) (i : ℕ) :
    MvPowerSeries.coeff (pairIdx i i) (f - uvSwapEquiv f) = 0 := by
  rw [map_sub, coeff_uvSwapEquiv, sub_self]

def oddPart (f : MvPowerSeries (Fin 2) W) : MvPowerSeries (Fin 2) W :=
  antiDiagSolve (f - uvSwapEquiv f)

def symPart (f : MvPowerSeries (Fin 2) W) : MvPowerSeries (Fin 2) W :=
  f - oddPart f * MvPowerSeries.X 0

theorem oddPart_mul_X_zero_sub_X_one (f : MvPowerSeries (Fin 2) W) :
    oddPart f * (MvPowerSeries.X 0 - MvPowerSeries.X 1) = f - uvSwapEquiv f :=
  antiDiagSolve_mul_X_zero_sub_X_one (uvSwapEquiv_sub_uvSwapEquiv f)
    (coeff_diag_sub_uvSwapEquiv f)

theorem uvSwapEquiv_oddPart (f : MvPowerSeries (Fin 2) W) :
    uvSwapEquiv (oddPart f) = oddPart f :=
  uvSwapEquiv_antiDiagSolve (uvSwapEquiv_sub_uvSwapEquiv f)
    (coeff_diag_sub_uvSwapEquiv f)

theorem uvSwapEquiv_symPart (f : MvPowerSeries (Fin 2) W) :
    uvSwapEquiv (symPart f) = symPart f := by
  have h1 : uvSwapEquiv (symPart f)
      = uvSwapEquiv f - oddPart f * MvPowerSeries.X 1 := by
    rw [symPart, map_sub, map_mul, uvSwapEquiv_oddPart, uvSwapEquiv_X_zero]
  rw [h1, eq_comm, ← sub_eq_zero]
  calc symPart f - (uvSwapEquiv f - oddPart f * MvPowerSeries.X 1)
      = (f - uvSwapEquiv f)
        - oddPart f * (MvPowerSeries.X 0 - MvPowerSeries.X 1) := by
        rw [symPart]; ring
    _ = 0 := by rw [oddPart_mul_X_zero_sub_X_one]; ring

theorem symPart_add_oddPart_mul_X_zero (f : MvPowerSeries (Fin 2) W) :
    symPart f + oddPart f * MvPowerSeries.X 0 = f := by
  rw [symPart]; ring

theorem exists_swapInvariant_rank_two_decomposition (f : MvPowerSeries (Fin 2) W) :
    ∃ A B : MvPowerSeries (Fin 2) W, SwapInvariant A ∧ SwapInvariant B ∧
      f = A + B * MvPowerSeries.X 0 :=
  ⟨symPart f, oddPart f,
    (swapInvariant_iff_uvSwapEquiv_eq _).mpr (uvSwapEquiv_symPart f),
    (swapInvariant_iff_uvSwapEquiv_eq _).mpr (uvSwapEquiv_oddPart f),
    (symPart_add_oddPart_mul_X_zero f).symm⟩

end Decomposition
p2m_reactivate "P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve.SymmetricTwoVars P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve"

section QuotientSpan

variable {W : Type u} [CommRing W]

theorem mk_mem_fixedSubring_of_uvSwapEquiv_eq (π : W) {F : MvPowerSeries (Fin 2) W}
    (hF : uvSwapEquiv F = F) :
    mk π F ∈ fixedSubring π := by
  rw [mem_fixedSubring_iff, crossingSwap_mk, hF]

theorem exists_mem_fixedSubring_decomposition (π : W) (x : UVCrossingModel W π) :
    ∃ a b : UVCrossingModel W π, a ∈ fixedSubring π ∧ b ∈ fixedSubring π ∧
      x = a + b * U π := by
  obtain ⟨F, rfl⟩ := mk_surjective π x
  refine ⟨mk π (symPart F), mk π (oddPart F),
    mk_mem_fixedSubring_of_uvSwapEquiv_eq π (uvSwapEquiv_symPart F),
    mk_mem_fixedSubring_of_uvSwapEquiv_eq π (uvSwapEquiv_oddPart F), ?_⟩
  have hU : U π = mk π (MvPowerSeries.X 0) := rfl
  rw [hU, ← map_mul, ← map_add, symPart_add_oddPart_mul_X_zero]

theorem span_one_U_eq_top (π : W) :
    Submodule.span (fixedSubring π) ({1, U π} : Set (UVCrossingModel W π)) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨a, b, ha, hb, rfl⟩ := exists_mem_fixedSubring_decomposition π x
  have hx : a + b * U π
      = (⟨a, ha⟩ : fixedSubring π) • (1 : UVCrossingModel W π)
        + (⟨b, hb⟩ : fixedSubring π) • U π := by
    rw [Algebra.smul_def, Algebra.smul_def, algebraMap_fixedSubring_eq_subtype]
    simp
  rw [hx]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem _ rfl)))

theorem moduleFinite_fixedSubring' (π : W) :
    Module.Finite (fixedSubring π) (UVCrossingModel W π) := by
  classical
  refine ⟨⟨{1, U π}, ?_⟩⟩
  rw [Finset.coe_insert, Finset.coe_singleton]
  exact span_one_U_eq_top π

theorem span_singleton_one_ne_top (π : W) [Nontrivial (W ⧸ Ideal.span {π})] :
    Submodule.span (fixedSubring π) ({1} : Set (UVCrossingModel W π)) ≠ ⊤ := by
  intro htop
  have hU : U π ∈ Submodule.span (fixedSubring π)
      ({1} : Set (UVCrossingModel W π)) := by
    rw [htop]; exact Submodule.mem_top
  rw [Submodule.mem_span_singleton] at hU
  obtain ⟨r, hr⟩ := hU
  apply U_notMem_fixedSubring π
  rw [← hr, Algebra.smul_def, algebraMap_fixedSubring_eq_subtype, mul_one]
  exact SetLike.coe_mem r

end QuotientSpan
p2m_reactivate "P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve.SymmetricTwoVars P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve"

end UVCrossingModel
p2m_reactivate "P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve.SymmetricTwoVars P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve"

end
p2m_reactivate "P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve.SymmetricTwoVars P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve"

end ModularCurve
p2m_reactivate "P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve.SymmetricTwoVars P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve"

open _root_.ModularCurve _root_.P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve _root_.ModularCurve.UVCrossingModel _root_.P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X.ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] (f : MvPowerSeries (Fin 2) W) :
    ∃ A B : MvPowerSeries (Fin 2) W, MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) A = A ∧ MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) B = B ∧ f = A + B * MvPowerSeries.X 0 :=
  ModularCurve.UVCrossingModel.exists_swapInvariant_rank_two_decomposition f

end S_MvPowerSeries_exists_rename_swap_eq_add_mul_X
end P2MW
export P2MW.S_MvPowerSeries_exists_rename_swap_eq_add_mul_X (solution)

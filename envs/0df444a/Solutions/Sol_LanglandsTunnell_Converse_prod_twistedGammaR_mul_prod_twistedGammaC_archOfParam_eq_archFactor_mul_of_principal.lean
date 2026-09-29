-- Prove2me | solution 1 for LanglandsTunnell.Converse.prod_twistedGammaR_mul_prod_twistedGammaC_archOfParam_eq_archFactor_mul_of_principal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/61c0d8d7-2e99-5d3c-8f6b-c4d988fce20d

import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_prod_twistedGammaR_mul_prod_twistedGammaC_archOfParam_eq_archFactor_mul_of_principal

set_option autoImplicit false

open NumberField LanglandsTunnell LanglandsTunnell.Converse Complex

namespace TwistedGammaPress

variable {K : Type} [Field K]

theorem sum_isReal_of_three {M : Type*} [AddCommMonoid M]
    (instR : Fintype {w : InfinitePlace K // w.IsReal})
    (w₀ w₁ w₂ : InfinitePlace K) (h₀ : w₀.IsReal) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal)
    (h01 : w₀ ≠ w₁) (h02 : w₀ ≠ w₂) (h12 : w₁ ≠ w₂)
    (hall : ∀ w : InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂)
    (f : {w : InfinitePlace K // w.IsReal} → M) :
    (@Finset.univ _ instR).sum f = f ⟨w₀, h₀⟩ + f ⟨w₁, h₁⟩ + f ⟨w₂, h₂⟩ := by
  classical
  have huniv : (@Finset.univ _ instR) =
      ({⟨w₀, h₀⟩, ⟨w₁, h₁⟩, ⟨w₂, h₂⟩} : Finset {w : InfinitePlace K // w.IsReal}) := by
    ext x
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton]
    rcases hall x.1 with h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Subtype.ext h))
  rw [huniv, Finset.sum_insert, Finset.sum_pair, add_assoc]
  · exact fun h => h12 (congrArg Subtype.val h)
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => h01 (congrArg Subtype.val h), fun h => h02 (congrArg Subtype.val h)⟩

theorem sum_isComplex_of_three {M : Type*} [AddCommMonoid M]
    (instC : Fintype {w : InfinitePlace K // w.IsComplex})
    (w₀ w₁ w₂ : InfinitePlace K) (h₀ : w₀.IsReal) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal)
    (hall : ∀ w : InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂)
    (f : {w : InfinitePlace K // w.IsComplex} → M) :
    (@Finset.univ _ instC).sum f = 0 := by
  have hempty : IsEmpty {w : InfinitePlace K // w.IsComplex} := ⟨fun x => by
    have hx : x.1.IsComplex := x.2
    rcases hall x.1 with h | h | h <;> rw [h] at hx
    · exact InfinitePlace.not_isReal_iff_isComplex.mpr hx h₀
    · exact InfinitePlace.not_isReal_iff_isComplex.mpr hx h₁
    · exact InfinitePlace.not_isReal_iff_isComplex.mpr hx h₂⟩
  rw [@Finset.univ_eq_empty _ instC hempty, Finset.sum_empty]

theorem sum_isReal_of_one_one {M : Type*} [AddCommMonoid M]
    (instR : Fintype {w : InfinitePlace K // w.IsReal})
    (w₀ wC : InfinitePlace K) (h₀ : w₀.IsReal) (hC : wC.IsComplex)
    (hall : ∀ w : InfinitePlace K, w = wC ∨ w = w₀)
    (f : {w : InfinitePlace K // w.IsReal} → M) :
    (@Finset.univ _ instR).sum f = f ⟨w₀, h₀⟩ := by
  classical
  have huniv : (@Finset.univ _ instR) = ({⟨w₀, h₀⟩} : Finset {w : InfinitePlace K // w.IsReal}) := by
    ext x
    simp only [Finset.mem_univ, true_iff, Finset.mem_singleton]
    rcases hall x.1 with h | h
    · exact absurd (h ▸ x.2 : wC.IsReal) (InfinitePlace.not_isReal_iff_isComplex.mpr hC)
    · exact Subtype.ext h
  rw [huniv, Finset.sum_singleton]

theorem sum_isComplex_of_one_one {M : Type*} [AddCommMonoid M]
    (instC : Fintype {w : InfinitePlace K // w.IsComplex})
    (w₀ wC : InfinitePlace K) (h₀ : w₀.IsReal) (hC : wC.IsComplex)
    (hall : ∀ w : InfinitePlace K, w = wC ∨ w = w₀)
    (f : {w : InfinitePlace K // w.IsComplex} → M) :
    (@Finset.univ _ instC).sum f = f ⟨wC, hC⟩ := by
  classical
  have huniv : (@Finset.univ _ instC) = ({⟨wC, hC⟩} : Finset {w : InfinitePlace K // w.IsComplex}) := by
    ext x
    simp only [Finset.mem_univ, true_iff, Finset.mem_singleton]
    rcases hall x.1 with h | h
    · exact Subtype.ext h
    · exact absurd (h ▸ x.2 : w₀.IsComplex) (InfinitePlace.not_isComplex_iff_isReal.mpr h₀)
  rw [huniv, Finset.sum_singleton]

variable (K) [NumberField K]

theorem twistedGammaR_of_three (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (w₀ w₁ w₂ : InfinitePlace K) (h₀ : w₀.IsReal) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal)
    (h01 : w₀ ≠ w₁) (h02 : w₀ ≠ w₂) (h12 : w₁ ≠ w₂)
    (hall : ∀ w : InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂) :
    twistedGammaR K archR uR aR =
      ((archR w₀ h₀).twist (uR w₀ h₀) (aR w₀ h₀)).gammaR +
        ((archR w₁ h₁).twist (uR w₁ h₁) (aR w₁ h₁)).gammaR +
        ((archR w₂ h₂).twist (uR w₂ h₂) (aR w₂ h₂)).gammaR := by
  unfold twistedGammaR
  exact sum_isReal_of_three _ w₀ w₁ w₂ h₀ h₁ h₂ h01 h02 h12 hall _

theorem twistedGammaC_of_three (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (w₀ w₁ w₂ : InfinitePlace K) (h₀ : w₀.IsReal) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal)
    (h01 : w₀ ≠ w₁) (h02 : w₀ ≠ w₂) (h12 : w₁ ≠ w₂)
    (hall : ∀ w : InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂) :
    twistedGammaC K archR archC uR aR uC kC =
      ((archR w₀ h₀).twist (uR w₀ h₀) (aR w₀ h₀)).gammaC +
        ((archR w₁ h₁).twist (uR w₁ h₁) (aR w₁ h₁)).gammaC +
        ((archR w₂ h₂).twist (uR w₂ h₂) (aR w₂ h₂)).gammaC := by
  unfold twistedGammaC
  rw [sum_isReal_of_three _ w₀ w₁ w₂ h₀ h₁ h₂ h01 h02 h12 hall,
    sum_isComplex_of_three _ w₀ w₁ w₂ h₀ h₁ h₂ hall, add_zero]

theorem twistedGammaR_of_one_one (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (w₀ wC : InfinitePlace K) (h₀ : w₀.IsReal) (hC : wC.IsComplex)
    (hall : ∀ w : InfinitePlace K, w = wC ∨ w = w₀) :
    twistedGammaR K archR uR aR = ((archR w₀ h₀).twist (uR w₀ h₀) (aR w₀ h₀)).gammaR := by
  unfold twistedGammaR
  exact sum_isReal_of_one_one _ w₀ wC h₀ hC hall _

theorem twistedGammaC_of_one_one (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (w₀ wC : InfinitePlace K) (h₀ : w₀.IsReal) (hC : wC.IsComplex)
    (hall : ∀ w : InfinitePlace K, w = wC ∨ w = w₀) :
    twistedGammaC K archR archC uR aR uC kC =
      ((archR w₀ h₀).twist (uR w₀ h₀) (aR w₀ h₀)).gammaC +
        ((archC wC hC).twist (uC wC hC) (kC wC hC)).gammaC := by
  unfold twistedGammaC
  rw [sum_isReal_of_one_one _ w₀ wC h₀ hC hall, sum_isComplex_of_one_one _ w₀ wC h₀ hC hall]

theorem archFactor_principal_twist (ν₁ ν₂ u : ℂ) (a₁ a₂ c : ZMod 2) (s : ℂ) :
    ((RealArchParam.principal ν₁ a₁ ν₂ a₂).twist u c).archFactor s =
      Gammaℝ (s + (ν₁ + u + signShift (a₁ + c))) * Gammaℝ (s + (ν₂ + u + signShift (a₂ + c))) := by
  simp [RealArchParam.twist, RealArchParam.archFactor, RealArchParam.gammaR, RealArchParam.gammaC]

theorem archFactor_discrete_twist (u₀ u : ℂ) (n : ℕ) (hn : 1 ≤ n) (c : ZMod 2) (s : ℂ) :
    ((RealArchParam.discrete u₀ n hn).twist u c).archFactor s = Gammaℂ (s + (u₀ + u + (n : ℂ) / 2)) := by
  simp [RealArchParam.twist, RealArchParam.archFactor, RealArchParam.gammaR, RealArchParam.gammaC]

theorem prod_map_Gammaℝ_gammaR_principal_twist (ν₁ ν₂ u : ℂ) (a₁ a₂ c : ZMod 2) (s : ℂ) :
    ((((RealArchParam.principal ν₁ a₁ ν₂ a₂).twist u c).gammaR).map fun x => Gammaℝ (s + x)).prod =
      Gammaℝ (s + (ν₁ + u + signShift (a₁ + c))) * Gammaℝ (s + (ν₂ + u + signShift (a₂ + c))) := by
  simp [RealArchParam.twist, RealArchParam.gammaR]

theorem gammaC_principal_twist (ν₁ ν₂ u : ℂ) (a₁ a₂ c : ZMod 2) :
    ((RealArchParam.principal ν₁ a₁ ν₂ a₂).twist u c).gammaC = 0 := by
  simp [RealArchParam.twist, RealArchParam.gammaC]

theorem archFactor_principal_twist_mul_swap (ν₁ ν₂ u₁ u₂ : ℂ) (a₁ a₂ c₁ c₂ : ZMod 2) (s : ℂ) :
    ((RealArchParam.principal ν₁ a₁ ν₂ a₂).twist u₁ c₁).archFactor s *
        ((RealArchParam.principal ν₁ a₁ ν₂ a₂).twist u₂ c₂).archFactor s =
      ((RealArchParam.principal u₁ c₁ u₂ c₂).twist ν₁ a₁).archFactor s *
        ((RealArchParam.principal u₁ c₁ u₂ c₂).twist ν₂ a₂).archFactor s := by
  simp only [archFactor_principal_twist]
  rw [add_comm u₁ ν₁, add_comm u₂ ν₁, add_comm u₁ ν₂, add_comm u₂ ν₂, add_comm c₁ a₁, add_comm c₂ a₁,
    add_comm c₁ a₂, add_comm c₂ a₂]
  ring

theorem press_of_three (p₁ p₂ : ℂ) (b₁ b₂ : ZMod 2)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (U : ∀ w : InfinitePlace K, w.IsReal → ℂ) (A : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (V : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (k : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (w₀ w₁ w₂ : InfinitePlace K) (h₀ : w₀.IsReal) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal)
    (h01 : w₀ ≠ w₁) (h02 : w₀ ≠ w₂) (h12 : w₁ ≠ w₂)
    (hall : ∀ w : InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂) (s : ℂ) :
    ((twistedGammaR K (fun _ _ => RealArchParam.principal p₁ b₁ p₂ b₂) U A).map
          fun x => Gammaℝ (s + x)).prod *
      ((twistedGammaC K (fun _ _ => RealArchParam.principal p₁ b₁ p₂ b₂) archC U A V k).map
          fun x => Gammaℂ (s + x)).prod =
    ((RealArchParam.principal p₁ b₁ p₂ b₂).twist (U w₀ h₀) (A w₀ h₀)).archFactor s *
      (((RealArchParam.principal (U w₁ h₁) (A w₁ h₁) (U w₂ h₂) (A w₂ h₂)).twist p₁ b₁).archFactor s *
        ((RealArchParam.principal (U w₁ h₁) (A w₁ h₁) (U w₂ h₂) (A w₂ h₂)).twist p₂ b₂).archFactor s) := by
  rw [twistedGammaR_of_three K _ U A w₀ w₁ w₂ h₀ h₁ h₂ h01 h02 h12 hall,
    twistedGammaC_of_three K _ archC U A V k w₀ w₁ w₂ h₀ h₁ h₂ h01 h02 h12 hall,
    ← archFactor_principal_twist_mul_swap]
  simp only [gammaC_principal_twist, add_zero, Multiset.map_zero, Multiset.prod_zero, mul_one,
    Multiset.map_add, Multiset.prod_add, prod_map_Gammaℝ_gammaR_principal_twist,
    archFactor_principal_twist]
  ring

theorem press_of_one_one_discrete (p₁ p₂ : ℂ) (b₁ b₂ : ZMod 2)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (U : ∀ w : InfinitePlace K, w.IsReal → ℂ) (A : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (V : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (k : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (w₀ wC : InfinitePlace K) (h₀ : w₀.IsReal) (hC : wC.IsComplex)
    (hall : ∀ w : InfinitePlace K, w = wC ∨ w = w₀)
    (harchC : ((archC wC hC).twist (V wC hC) (k wC hC)).gammaC =
      {p₁ + V wC hC + ((k wC hC).natAbs : ℂ) / 2, p₂ + V wC hC + ((k wC hC).natAbs : ℂ) / 2})
    (n : ℕ) (hn : 1 ≤ n) (hnk : n = (k wC hC).natAbs) (s : ℂ) :
    ((twistedGammaR K (fun _ _ => RealArchParam.principal p₁ b₁ p₂ b₂) U A).map
          fun x => Gammaℝ (s + x)).prod *
      ((twistedGammaC K (fun _ _ => RealArchParam.principal p₁ b₁ p₂ b₂) archC U A V k).map
          fun x => Gammaℂ (s + x)).prod =
    ((RealArchParam.principal p₁ b₁ p₂ b₂).twist (U w₀ h₀) (A w₀ h₀)).archFactor s *
      (((RealArchParam.discrete (V wC hC) n hn).twist p₁ b₁).archFactor s *
        ((RealArchParam.discrete (V wC hC) n hn).twist p₂ b₂).archFactor s) := by
  rw [twistedGammaR_of_one_one K _ U A w₀ wC h₀ hC hall,
    twistedGammaC_of_one_one K _ archC U A V k w₀ wC h₀ hC hall, harchC]
  simp only [gammaC_principal_twist, zero_add, Multiset.insert_eq_cons, Multiset.map_cons,
    Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton,
    prod_map_Gammaℝ_gammaR_principal_twist, archFactor_principal_twist, archFactor_discrete_twist, ← hnk]
  rw [add_comm (V wC hC) p₁, add_comm (V wC hC) p₂]

theorem press_of_one_one_principal (p₁ p₂ : ℂ) (b₁ b₂ : ZMod 2)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (U : ∀ w : InfinitePlace K, w.IsReal → ℂ) (A : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (V : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (k : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (w₀ wC : InfinitePlace K) (h₀ : w₀.IsReal) (hC : wC.IsComplex)
    (hall : ∀ w : InfinitePlace K, w = wC ∨ w = w₀)
    (harchC : ((archC wC hC).twist (V wC hC) (k wC hC)).gammaC =
      {p₁ + V wC hC + ((k wC hC).natAbs : ℂ) / 2, p₂ + V wC hC + ((k wC hC).natAbs : ℂ) / 2})
    (hk0 : k wC hC = 0) (s : ℂ) :
    ((twistedGammaR K (fun _ _ => RealArchParam.principal p₁ b₁ p₂ b₂) U A).map
          fun x => Gammaℝ (s + x)).prod *
      ((twistedGammaC K (fun _ _ => RealArchParam.principal p₁ b₁ p₂ b₂) archC U A V k).map
          fun x => Gammaℂ (s + x)).prod =
    ((RealArchParam.principal p₁ b₁ p₂ b₂).twist (U w₀ h₀) (A w₀ h₀)).archFactor s *
      (((RealArchParam.principal (V wC hC) 0 (V wC hC) 1).twist p₁ b₁).archFactor s *
        ((RealArchParam.principal (V wC hC) 0 (V wC hC) 1).twist p₂ b₂).archFactor s) := by
  rw [twistedGammaR_of_one_one K _ U A w₀ wC h₀ hC hall,
    twistedGammaC_of_one_one K _ archC U A V k w₀ wC h₀ hC hall, harchC]
  simp only [gammaC_principal_twist, zero_add, Multiset.insert_eq_cons, Multiset.map_cons,
    Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton,
    prod_map_Gammaℝ_gammaR_principal_twist, archFactor_principal_twist, hk0, Int.natAbs_zero,
    Nat.cast_zero, zero_div, add_zero]
  have d₁ := RealArchParam.Gammaℝ_signShift_mul (s + (p₁ + V wC hC)) b₁
  have d₂ := RealArchParam.Gammaℝ_signShift_mul (s + (p₂ + V wC hC)) b₂
  rw [add_comm (V wC hC) p₁, add_comm (V wC hC) p₂, add_comm (1 : ZMod 2) b₁, add_comm (1 : ZMod 2) b₂,
    ← d₁, ← d₂]
  simp only [add_assoc]

end TwistedGammaPress

open TwistedGammaPress in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (w₀ : InfinitePlace K) (h₀ : w₀.IsReal)
    (P₂ : RealArchParam)
    (hP₂ : ((∃ (w₁ w₂ : InfinitePlace K) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal),
          w₀ ≠ w₁ ∧ w₀ ≠ w₂ ∧ w₁ ≠ w₂ ∧ (∀ w : InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂) ∧
          P₂ = RealArchParam.principal (uR w₁ h₁) (aR w₁ h₁) (uR w₂ h₂) (aR w₂ h₂)) ∨
        (∃ (wC : InfinitePlace K) (hC : wC.IsComplex), (∀ w : InfinitePlace K, w = wC ∨ w = w₀) ∧
          ((∃ hk : kC wC hC ≠ 0, P₂ = RealArchParam.discrete (uC wC hC) (kC wC hC).natAbs (Int.natAbs_pos.mpr hk)) ∨
           (kC wC hC = 0 ∧ P₂ = RealArchParam.principal (uC wC hC) 0 (uC wC hC) 1)))))
    (P : RealArchParam) (ν₁ ν₂ : ℂ) (a₁ a₂ : ZMod 2) (hP : P = RealArchParam.principal ν₁ a₁ ν₂ a₂)
    (s : ℂ) :
    ((twistedGammaR K (archOfParamR K P) uR aR).map fun x => Complex.Gammaℝ (s + x)).prod *
        ((twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC).map
          fun x => Complex.Gammaℂ (s + x)).prod =
      (P.twist (uR w₀ h₀) (aR w₀ h₀)).archFactor s *
        ((P₂.twist ν₁ a₁).archFactor s * (P₂.twist ν₂ a₂).archFactor s) := by
  subst hP
  rcases hP₂ with ⟨w₁, w₂, h₁, h₂, h01, h02, h12, hall, rfl⟩ | ⟨wC, hC, hall, hb⟩
  · exact press_of_three K ν₁ ν₂ a₁ a₂ (archOfParamC K _) uR aR uC kC w₀ w₁ w₂ h₀ h₁ h₂ h01 h02 h12 hall s
  · have harchC : ((archOfParamC K (RealArchParam.principal ν₁ a₁ ν₂ a₂) wC hC).twist (uC wC hC) (kC wC hC)).gammaC =
        {ν₁ + uC wC hC + ((kC wC hC).natAbs : ℂ) / 2, ν₂ + uC wC hC + ((kC wC hC).natAbs : ℂ) / 2} := by
      simp [archOfParamC, RealArchParam.baseChange, ComplexArchParam.twist, ComplexArchParam.gammaC]
    rcases hb with ⟨hk, rfl⟩ | ⟨hk0, rfl⟩
    · exact press_of_one_one_discrete K ν₁ ν₂ a₁ a₂ (archOfParamC K _) uR aR uC kC w₀ wC h₀ hC hall harchC
        _ _ rfl s
    · exact press_of_one_one_principal K ν₁ ν₂ a₁ a₂ (archOfParamC K _) uR aR uC kC w₀ wC h₀ hC hall harchC
        hk0 s

end S_LanglandsTunnell_Converse_prod_twistedGammaR_mul_prod_twistedGammaC_archOfParam_eq_archFactor_mul_of_principal
end P2MW
export P2MW.S_LanglandsTunnell_Converse_prod_twistedGammaR_mul_prod_twistedGammaC_archOfParam_eq_archFactor_mul_of_principal (solution)

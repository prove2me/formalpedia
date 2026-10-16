-- Prove2me | solution 1 for OAI.ShortEgyptian.upper_at_scale
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T04:13:06.20366+00:00
-- url     : https://prove2.me/submissions/4603c74a-7c86-4f57-b551-3cb908f7ce99

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/UpperAssembly.lean:L58-L111
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.upper_at_scale. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeLists
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeProducts
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_HammingDistance
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SamplePartitions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ProductCorrelations
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_LevelSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListConstruction
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleGeometry
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ResidueSystem
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TerminalScale
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DescentSets
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_MomentRecurrence
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Density
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_GreedyPreparation
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_UpperAssembly
import Theorems.Thm_OAI_ShortEgyptian_floor_multiple
import Theorems.Thm_OAI_ShortEgyptian_greedy_length_bound
import Theorems.Thm_OAI_ShortEgyptian_prepare_denominator
import Theorems.Thm_OAI_ShortEgyptian_remove_repetitions

-- ---- from OAI.NumberTheory.ShortEgyptian.Basic ----
namespace OAI

namespace ShortEgyptian

theorem unitSum_scale (g : ℕ) (ns : List ℕ) :
    unitSum (ns.map (g * ·)) = unitSum ns / (g : ℚ) := by
  induction ns with
  | nil => simp
  | cons n ns ih =>
    simp only [List.map_cons, unitSum_cons, ih, Nat.cast_mul]
    rw [add_div]
    congr 1
    simp [div_eq_mul_inv, mul_comm]

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.Density ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical Filter Topology

lemma densityConstant_pos : 0 < densityConstant := by
  have h₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : 0 < Real.log (10000/9999:ℝ) := Real.log_pos (by norm_num)
  dsimp [densityConstant,terminalConstant]
  positivity

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.GreedyPreparation ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

lemma greedy_power_cap (S : ℝ) (hS : 0<S) :
    Real.exp ((dimC:ℝ)*S) ≤ Real.exp ((2:ℝ)^greedySteps S*Real.log 2) := by
  have h₂ : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hD : (0:ℝ)<dimC := by norm_num [dimC,dimX,dimM]
  have hx : 0 < (dimC:ℝ)*S/Real.log 2 := div_pos (mul_pos hD hS) h₂
  have hh := (div_le_iff₀ h₂).mp (Nat.le_ceil (Real.log ((dimC:ℝ)*S/Real.log 2)/Real.log 2))
  change Real.log ((dimC:ℝ)*S/Real.log 2) ≤ (greedySteps S:ℝ)*Real.log 2 at hh
  have he := Real.exp_le_exp.mpr hh
  rw [Real.exp_log hx,Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)] at he
  exact Real.exp_le_exp.mpr ((div_le_iff₀ h₂).mp he)

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.DenseSplit ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical

lemma dense_split_nat (G : Finset ℕ) (N n : ℕ) (hn : n ≤ N)
    (hbad : 2*(Icc 1 N \ G).card < n-1) :
    ∃ u ∈ G, ∃ v ∈ G, n=u+v := by
  by_contra h
  let B := Ico 1 n \ G
  have hcov : Ico 1 n ⊆ B ∪ B.image (n-·) := by
    intro u hu
    by_cases huG : u ∈ G
    · have huv := mem_Ico.mp hu
      have hv : n-u ∉ G := by
        intro hv
        exact h ⟨u,huG,n-u,hv,by omega⟩
      have hvB : n-u ∈ B := mem_sdiff.mpr ⟨mem_Ico.mpr (by omega),hv⟩
      exact mem_union.mpr (Or.inr (mem_image.mpr ⟨n-u,hvB,by omega⟩))
    · exact mem_union.mpr (Or.inl (mem_sdiff.mpr ⟨hu,huG⟩))
  have hB : B ⊆ Icc 1 N \ G := by
    intro u hu
    obtain ⟨hu,huG⟩ := mem_sdiff.mp hu
    obtain ⟨hu1,hun⟩ := mem_Ico.mp hu
    exact mem_sdiff.mpr ⟨mem_Icc.mpr ⟨hu1,le_trans hun.le hn⟩,huG⟩
  have hh := (card_le_card hcov).trans ((card_union_le B (B.image (n-·))).trans
    (add_le_add (card_le_card hB) ((card_image_le).trans (card_le_card hB))))
  rw [Nat.card_Ico] at hh
  omega

lemma dense_split (X : ℝ) (hX : 4<X) (G : Finset ℕ) (n : ℕ)
    (hnlo : X/2 ≤ n) (hnhi : (n:ℝ) ≤ X)
    (hbad : ((Icc 1 ⌊X⌋₊ \ G).card:ℝ) ≤ X/8) :
    ∃ u ∈ G, ∃ v ∈ G, n=u+v := by
  have hnpos : 1≤n := by
    have hh : (1:ℝ)≤n := by linarith
    exact_mod_cast hh
  apply dense_split_nat G ⌊X⌋₊ n (Nat.le_floor hnhi)
  have hh : (2:ℝ)*((Icc 1 ⌊X⌋₊ \ G).card:ℝ) < (n:ℝ)-1 := by linarith
  have hh' : ((2*(Icc 1 ⌊X⌋₊ \ G).card:ℕ):ℝ) < ((n-1:ℕ):ℝ) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub hnpos,Nat.cast_one] using hh
  exact_mod_cast hh'

lemma isUnitSum_append {x y : ℚ} {xs ys : List ℕ}
    (hx : IsUnitSum x xs) (hy : IsUnitSum y ys) : IsUnitSum (x+y) (xs++ys) := by
  refine ⟨?_,?_⟩
  · intro n hn
    rcases List.mem_append.mp hn with hn | hn
    · exact hx.1 n hn
    · exact hy.1 n hn
  · rw [unitSum_append,hx.2,hy.2]

lemma isUnitSum_scale {x : ℚ} {xs : List ℕ} (h : IsUnitSum x xs)
    (g : ℕ) (hg : 0<g) : IsUnitSum (x/(g:ℚ)) (xs.map (g*·)) := by
  refine ⟨?_,?_⟩
  · intro n hn
    obtain ⟨m,hm,hmn⟩ := List.mem_map.mp hn
    subst n
    have hh := h.1 m hm
    nlinarith
  · rw [unitSum_scale,h.2]

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.UpperAssembly ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical Filter Topology

lemma dense_remainder (S : ℝ) (hS : 0<S) (hX : 4<Real.exp ((dimX:ℝ)*S))
    (C : ℕ) (hC : 0<C) (D : DenseData S C) (A : ℕ) (hA : 0<A)
    (hAb : (A:ℝ)≤Real.exp S) :
    ∃ ns, IsUnitSum ((A:ℚ)/C) ns ∧ (ns.length:ℝ)≤2*densityConstant*Real.log S := by
  let X := Real.exp ((dimX:ℝ)*S)
  let P := A*D.M
  have hM : 0<D.M := by exact_mod_cast (Real.exp_pos S).trans D.M_lower
  have hP : 0<P := Nat.mul_pos hA hM
  have hPX : (P:ℝ)≤X := by
    calc
      (P:ℝ) = (A:ℝ)*(D.M:ℝ) := by simp only [P,Nat.cast_mul]
      _ ≤ Real.exp S*Real.exp ((dimM:ℝ)*S) := mul_le_mul hAb D.M_upper (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp ((1+(dimM:ℝ))*S) := by rw [←Real.exp_add]; congr 1; ring
      _ ≤ X := by
        apply Real.exp_le_exp.mpr
        have heq : (dimX:ℝ) = (dimM:ℝ)+2 := by norm_num [dimX]
        rw [heq]
        nlinarith
  let g := ⌊X/(P:ℝ)⌋₊
  let n := g*P
  have hf := floor_multiple X P hP hPX
  change 0<g ∧ X/2≤(n:ℝ) ∧ (n:ℝ)≤X at hf
  obtain ⟨u,hu,v,hv,hn⟩ := dense_split X hX D.G n hf.2.1 hf.2.2 D.bad_card
  obtain ⟨xs,hxs,hxlen⟩ := D.expansion u hu
  obtain ⟨ys,hys,hylen⟩ := D.expansion v hv
  have hh := isUnitSum_scale (isUnitSum_append hxs hys) g hf.1
  have hMn : (D.M:ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hCn : (C:ℚ) ≠ 0 := by exact_mod_cast hC.ne'
  have hgn : (g:ℚ) ≠ 0 := by exact_mod_cast hf.1.ne'
  have hnQ : (u:ℚ)+v=(g:ℚ)*(A*D.M) := by
    have hh : u+v=g*(A*D.M) := hn.symm
    exact_mod_cast hh
  have heq : ((u:ℚ)/(D.M*C)+(v:ℚ)/(D.M*C))/(g:ℚ)=(A:ℚ)/C := by
    rw [←add_div,hnQ]
    field_simp
  rw [heq] at hh
  refine ⟨(xs++ys).map (g*·),hh,?_⟩
  simp only [List.length_map,List.length_append,Nat.cast_add]
  linarith

lemma upper_at_scale (S : ℝ) (hS : 2≤S) (hlog : 1≤Real.log S)
    (hdens : ∀ C : ℕ, Real.exp ((dimC:ℝ)*S)≤C → (C:ℝ)≤Real.exp (2*(dimC:ℝ)*S) → Nonempty (DenseData S C))
    (a b : ℕ) (ha : 0<a) (hab : a<b) (hb : (b:ℝ)=Real.exp S) :
    ∃ ns, IsExpansion a b ns ∧ (ns.length:ℝ)≤upperConstant*Real.log S := by
  have hSp : 0<S := by linarith
  have hDC : (1:ℝ)<dimC := by norm_num [dimC,dimX,dimM]
  have hDX : (1:ℝ)<dimX := by norm_num [dimX,dimM]
  let T := Real.exp ((dimC:ℝ)*S)
  have hT : 1<T := Real.one_lt_exp_iff.mpr (by nlinarith)
  have hbT : (b:ℝ)<T := by rw [hb]; apply Real.exp_lt_exp.mpr; nlinarith
  obtain ⟨xs,A,C,hxs,hxlen,hAa,hAC,heq,hstop⟩ := prepare_denominator a b ha hab T hT hbT
    (greedySteps S) (greedy_power_cap S hSp)
  have hxlenR : (xs.length:ℝ) ≤ greedyConstant*Real.log S :=
    (Nat.cast_le.mpr hxlen).trans (greedy_length_bound S (by linarith) hlog)
  have hlog0 : 0≤Real.log S := by linarith
  have hex : ∃ ns, IsUnitSum ((a:ℚ)/b) ns ∧ (ns.length:ℝ)≤upperConstant*Real.log S := by
    rcases hstop with hA0 | hCbound
    · refine ⟨xs,⟨hxs,?_⟩,?_⟩
      · simpa only [hA0,Nat.cast_zero,zero_div,add_zero] using heq.symm
      · dsimp [upperConstant]
        nlinarith [mul_nonneg densityConstant_pos.le hlog0]
    · have hChi : (C:ℝ)≤Real.exp (2*(dimC:ℝ)*S) := by
        apply hCbound.2.le.trans_eq
        dsimp [T]
        rw [pow_two,←Real.exp_add]
        congr 1
        ring
      obtain ⟨D⟩ := hdens C hCbound.1 hChi
      by_cases hA0 : A=0
      · refine ⟨xs,⟨hxs,?_⟩,?_⟩
        · simpa only [hA0,Nat.cast_zero,zero_div,add_zero] using heq.symm
        · dsimp [upperConstant]
          nlinarith [mul_nonneg densityConstant_pos.le hlog0]
      have hAp : 0<A := Nat.pos_of_ne_zero hA0
      have hC : 0<C := hAp.trans hAC
      have hX : 4<Real.exp ((dimX:ℝ)*S) := by
        have hadd := Real.add_one_le_exp ((dimX:ℝ)*S)
        have hD : (3:ℝ)≤dimX := by norm_num [dimX,dimM]
        nlinarith
      have hAb : (A:ℝ) ≤ Real.exp S := by rw [←hb]; exact_mod_cast hAa.trans hab.le
      obtain ⟨ys,hys,hylen⟩ := dense_remainder S hSp hX C hC D A hAp hAb
      refine ⟨xs++ys,⟨?_,?_⟩,?_⟩
      · intro n hn
        rcases List.mem_append.mp hn with hn | hn
        · exact hxs n hn
        · exact hys.1 n hn
      · rw [unitSum_append,hys.2]
        exact heq.symm
      · dsimp [upperConstant]
        simp only [List.length_append,Nat.cast_add]
        nlinarith
  obtain ⟨ns,hns,hlen⟩ := hex
  obtain ⟨ys,hys,hylen⟩ := remove_repetitions ha hab ns (fun n hn => by have := hns.1 n hn; omega) hns.2
  exact ⟨ys,hys,by simpa only [hylen] using hlen⟩

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq
open scoped BigOperators
open Finset Classical Filter Topology


theorem solution : type_of% @_root_.OAI.ShortEgyptian.upper_at_scale := @_root_.OAI.ShortEgyptian.upper_at_scale

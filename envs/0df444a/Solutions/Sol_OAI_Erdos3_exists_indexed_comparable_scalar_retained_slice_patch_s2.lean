-- Prove2me | solution 1 for OAI.Erdos3.exists_indexed_comparable_scalar_retained_slice_patch_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:45:53.442773+00:00
-- url     : https://prove2.me/submissions/1fd48408-eef7-42a5-a031-69769c133395

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B191
import Definitions.Def_OAIE3v2B193
import Definitions.Def_OAIE3v2B248
import Theorems.Thm_OAI_Erdos3_exists_indexed_comparable_scalar_shared_slice_tail_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseProductCardDeficit
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem denseProductDeficit_le_sum {I : Type*} (S : Finset I) (f : I → ℝ)
    (hf : ∀ i ∈ S, f i ∈ Set.Icc (0 : ℝ) 1) :
    1 - ∏ i ∈ S, f i ≤ ∑ i ∈ S, (1 - f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hfi := hf i (Finset.mem_insert_self i S)
    have hfS : ∀ j ∈ S, f j ∈ Set.Icc (0 : ℝ) 1 :=
      fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hprod : ∏ j ∈ S, f j ≤ 1 :=
      Finset.prod_le_one (fun j hj => (hfS j hj).1) (fun j hj => (hfS j hj).2)
    have hih := ih hfS
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    nlinarith [mul_nonneg (sub_nonneg.mpr hfi.2) (sub_nonneg.mpr hprod)]

theorem denseProductCardDeficit_le_sum {I : Type*} [Fintype I]
    (a b : I → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, b i ≤ a i) :
    1 - (∏ i, (b i : ℝ)) / (∏ i, (a i : ℝ)) ≤
      ∑ i, ((a i - b i : ℕ) : ℝ) / (a i : ℝ) := by
  have hpos (i : I) : (0 : ℝ) < a i := by exact_mod_cast ha i
  have hle (i : I) : (b i : ℝ) ≤ a i := by exact_mod_cast hb i
  have hfrac (i : I) : (b i : ℝ) / a i ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (Nat.cast_nonneg _) (hpos i).le, (div_le_one (hpos i)).mpr (hle i)⟩
  have h := denseProductDeficit_le_sum Finset.univ (fun i => (b i : ℝ) / a i)
    (fun i _ => hfrac i)
  rw [Finset.prod_div_distrib] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.cast_sub (hb i), sub_div, div_self (ne_of_gt (hpos i))]

theorem denseProductCardDeficit_le_card_mul {I : Type*} [Fintype I]
    (a b : I → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, b i ≤ a i)
    (η : ℝ) (hdeficit : ∀ i, ((a i - b i : ℕ) : ℝ) / (a i : ℝ) ≤ η) :
    1 - (∏ i, (b i : ℝ)) / (∏ i, (a i : ℝ)) ≤ (Fintype.card I : ℝ) * η := by
  calc
    _ ≤ ∑ i, ((a i - b i : ℕ) : ℝ) / (a i : ℝ) :=
      denseProductCardDeficit_le_sum a b ha hb
    _ ≤ ∑ _i : I, η := Finset.sum_le_sum (fun i _ => hdeficit i)
    _ = _ := by simp

theorem denseProductNatCardDeficit_le_card_mul {I : Type*} [Fintype I]
    (a b : I → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, b i ≤ a i)
    (η : ℝ) (hdeficit : ∀ i, ((a i - b i : ℕ) : ℝ) / (a i : ℝ) ≤ η) :
    1 - ((∏ i, b i : ℕ) : ℝ) / ((∏ i, a i : ℕ) : ℝ) ≤
      (Fintype.card I : ℝ) * η := by
  simpa only [Nat.cast_prod] using denseProductCardDeficit_le_card_mul a b ha hb η hdeficit

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceCountingCost
namespace OAI

section

namespace Erdos3

theorem residueIndexLength_eq_card (a b r v : ℤ) (hr : 0 < r) :
    residueIndexLength a b r v =
      (Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card := by
  rw [residueInterval_eq_map a b r v hr, Finset.card_map, Int.card_Ico]
  omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchProductBudget
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialPatch

variable {σ : Type*} {s d D E : ℕ}

theorem value_mem_Icc (A : PolynomialPatch σ s d) (t : σ → ℝ) :
    A.value t ∈ Set.Icc (0 : ℝ) 1 := (A.form.slots t).patchValue_mem_Icc A.kernel

end PolynomialPatch

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceNormalizedCell
namespace OAI

section

namespace Erdos3

namespace ResidueBoxSlice
variable {X : Type*} {N : X → ℕ} {q : ℕ}

theorem meshRounded_length_pos (S : ResidueBoxSlice N q) (hq : 0 < q) (M : ℕ)
    (hM : 0 < M) (hlen : ∀ i, 2 * M < S.length i) (i : X) :
    0 < (S.meshRounded hq M hM hlen).length i := by
  have h := (denseResidueMeshInterval (S.start i / q) (S.length i) M hM (hlen i)).1
  change 0 < M * ((S.start i / q + S.length i) / M) - M * (S.start i / q / M + 1)
  have := Nat.mul_lt_mul_of_pos_left h hM
  omega

theorem meshRounded_contained (S : ResidueBoxSlice N q) (hq : 0 < q) (M : ℕ)
    (hM : 0 < M) (hlen : ∀ i, 2 * M < S.length i) :
    ∃ offset : X → ℕ,
      (∀ i, (S.meshRounded hq M hM hlen).start i = S.start i + q * offset i) ∧
      (∀ i, offset i + (S.meshRounded hq M hM hlen).length i ≤ S.length i) ∧
      ∀ i, S.length i - (S.meshRounded hq M hM hlen).length i ≤ 2 * M := by
  refine ⟨fun i => M * (S.start i / q / M + 1) - S.start i / q, ?_, ?_, ?_⟩
  · intro i
    have h := (denseResidueMeshInterval (S.start i / q) (S.length i) M hM (hlen i)).2.1
    have he : M * (S.start i / q / M + 1) - S.start i / q + S.start i / q =
        M * (S.start i / q / M + 1) := by omega
    have hmod := Nat.mod_add_div (S.start i) q
    change _ + _ * _ = _ + _ * _
    nlinarith
  · intro i
    have h := denseResidueMeshInterval (S.start i / q) (S.length i) M hM (hlen i)
    dsimp only at h
    dsimp only [meshRounded]
    have hstart := h.2.1
    have hend := h.2.2.1
    have hmul := Nat.mul_le_mul_left M h.1.le
    omega
  · intro i
    exact (denseResidueMeshInterval (S.start i / q) (S.length i) M hM (hlen i)).2.2.2

end ResidueBoxSlice
end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

open _root_.MvPolynomial

variable {ι : Type*} {N : ι → ℕ} {q s d : ℕ}

theorem reparamPatch_value (A : ResidueBoxSlice N q) (P : PolynomialPatch ι s d)
    (j : ∀ i, Fin (A.length i)) :
    (A.reparamPatch P).value (fun i => ((j i).val : ℝ)) =
      P.value (fun i => ((A.point j i).val : ℝ)) := by
  rw [reparamPatch, PolynomialPatch.reparam_value]
  congr 1
  funext i
  simp [parameters, point]

end Erdos3.ResidueBoxSlice

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PhysicalSubboxResidueSlice
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem integerResidueBox_lengths_pos {I : Type*} (a b r v : I → ℤ)
    (hr : ∀ i, 0 < r i) (hbox : Nonempty (IntegerResidueBox a b r v)) :
    ∀ i, 0 < residueIndexLength (a i) (b i) (r i) (v i) := by
  obtain ⟨x⟩ := hbox
  intro i
  rw [residueIndexLength_eq_card (a i) (b i) (r i) (v i) (hr i)]
  exact Finset.card_pos.mpr ⟨(x i).val, (x i).property⟩

end Erdos3

end

section

namespace Erdos3

namespace ResidueBoxSlice

variable {X : Type*} (N H : X → ℕ) (lo a : X → ℤ) (M : ℕ)
    (hM : 0 < M) (hbox : PhysicalSubbox (fun _ => 0) N lo H)
    (hne : ∀ i, 0 < residueIndexLength (lo i) (lo i + H i) M (a i))

theorem ofPhysicalResidue_point_int
    (j : ∀ i, Fin ((ofPhysicalResidue N H lo a M hM hbox hne).length i)) (i : X) :
    (((ofPhysicalResidue N H lo a M hM hbox hne).point j i).val : ℤ) =
      a i + M * (residueIndexLower (lo i) M (a i) + (j i).val) := by
  change (((a i + M * residueIndexLower (lo i) M (a i)).toNat + M * (j i).val : ℕ) : ℤ) = _
  rw [Nat.cast_add, Nat.cast_mul,
    Int.toNat_of_nonneg (physicalResidue_start_nonneg N H lo a M hM hbox hne i)]
  ring

@[simp] theorem ofPhysicalResidueEquiv_val
    (j : ∀ i, Fin ((ofPhysicalResidue N H lo a M hM hbox hne).length i)) (i : X) :
    ((ofPhysicalResidueEquiv N H lo a M hM hbox hne j) i).val =
      (((ofPhysicalResidue N H lo a M hM hbox hne).point j i).val : ℤ) := by
  rw [ofPhysicalResidue_point_int]
  rfl

end ResidueBoxSlice
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedPatchReparam
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace WeightedParameterPatch

variable {σ : Type*} {p : σ → ℕ} {s d : ℕ}

theorem value_mem_Icc (A : WeightedParameterPatch σ p s d) (t : σ → ℝ) :
    A.value t ∈ Set.Icc (0 : ℝ) 1 := (A.form.slots t).patchValue_mem_Icc A.kernel

end WeightedParameterPatch

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchAmplification
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem RelativePatchSliceConclusion.mono {X : Type*} [Fintype X] {s : ℕ}
    {N : X → ℕ} {f : (X → ℤ) → ℝ} {target : ℝ} {rankBound rankBound' : ℕ}
    {cost cost' : ℝ} (h : RelativePatchSliceConclusion s N f target rankBound cost)
    (hrank : rankBound ≤ rankBound') (hcost : cost ≤ cost') :
    RelativePatchSliceConclusion s N f target rankBound' cost' := by
  obtain ⟨q, hq, S, d, A, hlength, hd, hcomplexity, hscore⟩ := h
  have he : Real.exp (-cost') ≤ Real.exp (-cost) :=
    Real.exp_le_exp.mpr (neg_le_neg hcost)
  exact ⟨q, hq, S, d, A, fun i =>
    (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _)).trans (hlength i),
    hd.trans hrank, hcomplexity.trans hcost, he.trans hscore⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativeChildSliceGeometry
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {X : Type*} {N : X → ℕ} {q : ℕ}

theorem stride_lt_two_div_density (S : ResidueBoxSlice N q) {i : X}
    (hql : 0 < q) (hlen : 2 ≤ S.length i) {δ : ℝ} (hδ : 0 < δ)
    (hdense : δ * (N i : ℝ) ≤ S.length i) : (q : ℝ) < 2 / δ := by
  have hh := S.inside i (S.length i - 1) (by omega)
  have hlast : (S.start i : ℝ) + (q : ℝ) * ((S.length i : ℝ) - 1) < N i := by
    have h : (S.start i : ℝ) + (q : ℝ) * ((S.length i - 1 : ℕ) : ℝ) < N i := by
      exact_mod_cast hh
    simpa only [Nat.cast_sub (by omega : 1 ≤ S.length i), Nat.cast_one] using h
  have hN : (0 : ℝ) < N i := by
    have : 0 < N i := lt_of_le_of_lt (Nat.zero_le _) hh
    exact_mod_cast this
  have hl : (2 : ℝ) ≤ S.length i := by exact_mod_cast hlen
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr hql
  have hstart : (0 : ℝ) ≤ S.start i := Nat.cast_nonneg _
  have hwidth : (q : ℝ) * S.length i < 2 * N i := by nlinarith
  have hd := mul_le_mul_of_nonneg_left hdense hq.le
  apply (lt_div_iff₀ hδ).mpr
  exact (mul_lt_mul_iff_right₀ hN).mp (by nlinarith)

end Erdos3.ResidueBoxSlice

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.DenseResidueMeshExponentialBudget
namespace OAI

section

namespace Erdos3

theorem denseResidueMesh_budget (n : ℕ) {δ ε C L : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) (hε₁ : ε ≤ 1) (hC : 1 ≤ C)
    (hL : 16 * ((n : ℝ) + 1) / (ε * δ) ≤ L) :
    0 < denseResidueMeshStep n δ ε L ∧
    C * L ≤ ((denseResidueMeshCap n δ ε C * denseResidueMeshStep n δ ε L : ℕ) : ℝ) ∧
    4 * (n : ℝ) * denseResidueMeshStep n δ ε L / (δ * L) ≤ ε / 2 ∧
    2 * (denseResidueMeshStep n δ ε L : ℝ) < δ * L ∧
    4 * (denseResidueMeshStep n δ ε L : ℝ) ≤ δ * L := by
  let M := denseResidueMeshStep n δ ε L
  let K := denseResidueMeshCap n δ ε C
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hd : 0 < ε * δ := mul_pos hε hδ
  have hb : 0 < 8 * ((n : ℝ) + 1) := by positivity
  have hlarge : 16 * ((n : ℝ) + 1) ≤ L * (ε * δ) :=
    (div_le_iff₀ hd).mp hL
  have hLpos : 0 < L := by
    have : 0 < L * (ε * δ) := lt_of_lt_of_le (by positivity) hlarge
    exact (mul_pos_iff_of_pos_right hd).mp this
  have hδL : 0 < δ * L := mul_pos hδ hLpos
  have ht : 2 ≤ ε * δ * L / (8 * ((n : ℝ) + 1)) := by
    apply (le_div_iff₀ hb).mpr
    nlinarith only [hlarge]
  have hMpos : 0 < M := Nat.floor_pos.mpr (by linarith only [ht])
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hMpos
  have hMnonneg : (0 : ℝ) ≤ M := by positivity
  have hMupper : (M : ℝ) * (8 * ((n : ℝ) + 1)) ≤ ε * δ * L := by
    apply (le_div_iff₀ hb).mp
    exact Nat.floor_le (by positivity)
  have hMlower : ε * δ * L ≤ 16 * ((n : ℝ) + 1) * M := by
    have hfloor := Nat.lt_floor_add_one (ε * δ * L / (8 * ((n : ℝ) + 1)))
    have hhalf : ε * δ * L / (8 * ((n : ℝ) + 1)) ≤ 2 * M := by
      change ε * δ * L / (8 * ((n : ℝ) + 1)) < (M : ℝ) + 1 at hfloor
      linarith only [hfloor, hMone]
    have := (div_le_iff₀ hb).mp hhalf
    nlinarith only [this]
  have hK : 16 * ((n : ℝ) + 1) * C ≤ (ε * δ) * K := by
    have hceil := Nat.le_ceil (16 * ((n : ℝ) + 1) * C / (ε * δ))
    have hbound : 16 * ((n : ℝ) + 1) * C / (ε * δ) ≤ (K : ℝ) := by
      dsimp [K, denseResidueMeshCap]
      push_cast
      linarith only [hceil]
    have := (div_le_iff₀ hd).mp hbound
    simpa [mul_comm] using this
  refine ⟨hMpos, ?_, ?_, ?_, ?_⟩
  · change C * L ≤ ((K * M : ℕ) : ℝ)
    rw [Nat.cast_mul]
    apply le_of_mul_le_mul_left _ hd
    calc
      (ε * δ) * (C * L) = C * (ε * δ * L) := by ring
      _ ≤ C * (16 * ((n : ℝ) + 1) * M) :=
        mul_le_mul_of_nonneg_left hMlower (by linarith only [hC])
      _ = (16 * ((n : ℝ) + 1) * C) * M := by ring
      _ ≤ ((ε * δ) * K) * M := mul_le_mul_of_nonneg_right hK hMnonneg
      _ = (ε * δ) * ((K : ℝ) * M) := by ring
  · apply (div_le_iff₀ hδL).mpr
    change 4 * (n : ℝ) * M ≤ ε / 2 * (δ * L)
    nlinarith only [hMupper, hMnonneg]
  · change 2 * (M : ℝ) < δ * L
    have hεL : ε * (δ * L) ≤ δ * L :=
      mul_le_of_le_one_left (le_of_lt hδL) hε₁
    nlinarith only [hMupper, hεL, hn, hMone]
  · change 4 * (M : ℝ) ≤ δ * L
    have hεL : ε * (δ * L) ≤ δ * L :=
      mul_le_of_le_one_left (le_of_lt hδL) hε₁
    nlinarith only [hMupper, hεL, hn, hMnonneg]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativeScalarPassageDiscount
namespace OAI

section

namespace Erdos3

theorem relativeScalarPassageSlack_bounds {τ : ℝ} (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) :
    0 < relativeScalarPassageSlack τ ∧ relativeScalarPassageSlack τ ≤ 1 := by
  have hd : 0 < 2 * (1 - τ) := by linarith
  exact ⟨div_pos hτ hd, (div_le_one hd).mpr (by linarith)⟩

theorem relativeScalarPassageSlack_level {τ Λ : ℝ} (hτ : τ < 1) :
    (1 + relativeScalarPassageSlack τ) * ((1 - τ) * Λ) = (1 - τ / 2) * Λ := by
  unfold relativeScalarPassageSlack
  have hd : 1 - τ ≠ 0 := by linarith
  field_simp
  ring

theorem relativeScalarPassageScore_le {τ Λ f g : ℝ}
    (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) (hΛ : 0 ≤ Λ) (hg : 0 ≤ g) :
    (f - Λ) * g ≤ f * g -
      (1 + relativeScalarPassageSlack τ) * ((1 - τ) * Λ) * g := by
  rw [relativeScalarPassageSlack_level (by linarith : τ < 1)]
  nlinarith [mul_nonneg (mul_nonneg hτ.le hΛ) hg]

theorem relativeScalarPassage_mesh_score
    {Ω : Type*} [Fintype Ω] (original mesh : FiniteProbabilityWeights Ω)
    (f g : Ω → ℝ) {τ Λ δ η : ℝ}
    (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) (hΛ : 0 ≤ Λ) (hg : ∀ x, 0 ≤ g x)
    (hscore : δ ≤ original.mean (fun x => (f x - Λ) * g x))
    (happrox : |original.mean (fun x => (f x - Λ) * g x) -
      mesh.mean (fun x => (f x - Λ) * g x)| ≤ η) :
    δ - η ≤ mesh.mean (fun x => f x * g x -
      (1 + relativeScalarPassageSlack τ) * ((1 - τ) * Λ) * g x) := by
  have hnear := (abs_le.mp happrox).2
  calc
    δ - η ≤ mesh.mean (fun x => (f x - Λ) * g x) := by linarith
    _ ≤ _ := mesh.mean_mono (fun x => relativeScalarPassageScore_le hτ hτhalf hΛ (hg x))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealFiniteZeroExtension
namespace OAI

section

namespace Erdos3

open scoped Classical

theorem realZeroExtendFinset_on {X : Type*} (S : Finset X) (f : X → ℝ)
    {x : X} (hx : x ∈ S) : realZeroExtendFinset S f x = f x := by
  simp only [realZeroExtendFinset, if_pos hx]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineMeshRetention
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem integerBoxUniformWeights_mean {J : Type*} [Fintype J] [DecidableEq J]
    (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j)
    (f : (∀ j, Finset.Ico (lo j) (hi j)) → ℝ) :
    (integerBoxUniformWeights lo hi hlen).mean f = 𝔼 x, f x := by
  let : ∀ j, Nonempty (Finset.Ico (lo j) (hi j)) :=
    fun j => ⟨⟨lo j, Finset.mem_Ico.mpr ⟨le_rfl, hlen j⟩⟩⟩
  have he : integerBoxUniformWeights lo hi hlen =
      FiniteProbabilityWeights.uniform (∀ j, Finset.Ico (lo j) (hi j)) := by
    apply FiniteProbabilityWeights.eq_of_weight_eq
    intro x
    change (∏ j, (Fintype.card (Finset.Ico (lo j) (hi j)) : ℝ)⁻¹) =
      (Fintype.card (∀ j, Finset.Ico (lo j) (hi j)) : ℝ)⁻¹
    rw [Fintype.card_pi, Nat.cast_prod, Finset.prod_inv_distrib]
  rw [he, FiniteProbabilityWeights.uniform_mean]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AnchoredReferenceDomination
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {α : Type*} [DecidableEq α]

theorem abs_expect_parent_sub_subset_le_Icc
    (S T : Finset α) (hT : T.Nonempty) (hTS : T ⊆ S)
    (f : α → ℝ) {a b : ℝ} (hf : ∀ x ∈ S, f x ∈ Set.Icc a b) :
    |(𝔼 x ∈ S, f x) - (𝔼 x ∈ T, f x)| ≤
      (b - a) * ((S.card - T.card : ℕ) : ℝ) / (S.card : ℝ) := by
  have hS : S.Nonempty := hT.mono hTS
  have hS0 : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_ne_zero
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hmeanlo : a ≤ 𝔼 x ∈ T, f x :=
    Finset.le_expect hT (fun x hx => (hf x (hTS hx)).1)
  have hmeanhi : (𝔼 x ∈ T, f x) ≤ b :=
    Finset.expect_le hT (fun x hx => (hf x (hTS hx)).2)
  have hsum : (∑ x ∈ S \ T, f x) + ∑ x ∈ T, f x = ∑ x ∈ S, f x :=
    Finset.sum_sdiff hTS
  have hc : ((S \ T).card : ℝ) + (T.card : ℝ) = S.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hTS
  have heq : (𝔼 x ∈ S, f x) - 𝔼 x ∈ T, f x =
      (∑ x ∈ S \ T, (f x - (𝔼 y ∈ T, f y))) / (S.card : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [sub_div, mul_div_assoc, Finset.expect_eq_sum_div_card S]
    have hTeq := Finset.card_mul_expect T f
    field_simp
    linear_combination -hsum - hTeq + (𝔼 y ∈ T, f y) * hc
  have hbound : |∑ x ∈ S \ T, (f x - (𝔼 y ∈ T, f y))| ≤
      (b - a) * ((S \ T).card : ℝ) := by
    calc
      _ ≤ ∑ x ∈ S \ T, |f x - (𝔼 y ∈ T, f y)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x ∈ S \ T, (b - a) := by
        apply Finset.sum_le_sum
        intro x hx
        have hfx := hf x (Finset.mem_sdiff.mp hx).1
        exact abs_le.mpr ⟨by linarith [hfx.1], by linarith [hfx.2]⟩
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  rw [heq, abs_div, abs_of_pos hSpos]
  exact (div_le_div_of_nonneg_right hbound hSpos.le).trans_eq (by rw [Finset.card_sdiff_of_subset hTS])

theorem abs_expect_parent_sub_subset_le_abs
    (S T : Finset α) (hT : T.Nonempty) (hTS : T ⊆ S)
    (f : α → ℝ) (hf : ∀ x ∈ S, |f x| ≤ 1) :
    |(𝔼 x ∈ S, f x) - (𝔼 x ∈ T, f x)| ≤
      2 * ((S.card - T.card : ℕ) : ℝ) / (S.card : ℝ) := by
  have h := abs_expect_parent_sub_subset_le_Icc S T hT hTS f
    (a := -1) (b := 1) (fun x hx => abs_le.mp (hf x hx))
  norm_num only [sub_neg_eq_add, one_add_one_eq_two] at h
  exact h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceUpperFailure
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem not_residueSliceUpperComparison_iff_exists_residue_slice
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    {h g : (σ → ℤ) → ℂ} {parent : σ → ℤ} {H : σ → ℕ} {P level ε : ℝ} :
    ¬ ResidueSliceUpperComparison h g parent H P level ε ↔
      ∃ (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (u : σ → ℤ),
        0 < M ∧ PhysicalSubbox parent H lo N ∧ ResidueSliceLogCostLE H lo N M u P ∧
          ε < (physicalResidueMean h lo N M u).re -
            level * (physicalResidueMean g lo N M u).re := by
  classical
  simp only [ResidueSliceUpperComparison, not_forall, not_le]
  constructor
  · rintro ⟨lo, N, M, u, hM, hbox, hcost, hscore⟩
    exact ⟨lo, N, M, u, hM, hbox, hcost, by linarith⟩
  · rintro ⟨lo, N, M, u, hM, hbox, hcost, hscore⟩
    exact ⟨lo, N, M, u, hM, hbox, hcost, by linarith⟩

theorem exists_residue_slice_of_not_upper
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    {h g : (σ → ℤ) → ℂ} {parent : σ → ℤ} {H : σ → ℕ} {P level ε : ℝ}
    (hfailure : ¬ ResidueSliceUpperComparison h g parent H P level ε) :
    ∃ (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (u : σ → ℤ),
      0 < M ∧ PhysicalSubbox parent H lo N ∧ ResidueSliceLogCostLE H lo N M u P ∧
        ε < (physicalResidueMean h lo N M u).re -
          level * (physicalResidueMean g lo N M u).re :=
  not_residueSliceUpperComparison_iff_exists_residue_slice.mp hfailure

theorem exists_nonempty_residue_slice_of_not_upper
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    {h g : (σ → ℤ) → ℂ} {parent : σ → ℤ} {H : σ → ℕ} {P level ε : ℝ}
    (hε : 0 ≤ ε) (hfailure : ¬ ResidueSliceUpperComparison h g parent H P level ε) :
    ∃ (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (u : σ → ℤ),
      0 < M ∧ PhysicalSubbox parent H lo N ∧ ResidueSliceLogCostLE H lo N M u P ∧
        Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) u) ∧
        (∀ j, 0 < residueIndexLength (lo j) (lo j + N j) M (u j)) ∧
        ε < (physicalResidueMean h lo N M u).re -
          level * (physicalResidueMean g lo N M u).re := by
  classical
  obtain ⟨lo, N, M, u, hM, hbox, hcost, hscore⟩ := exists_residue_slice_of_not_upper hfailure
  have hne : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) u) := by
    by_contra hempty
    have := not_nonempty_iff.mp hempty
    have hh : physicalResidueMean h lo N M u = 0 := by simp [physicalResidueMean]
    have hg : physicalResidueMean g lo N M u = 0 := by simp [physicalResidueMean]
    rw [hh, hg] at hscore
    simp only [Complex.zero_re, mul_zero, sub_zero] at hscore
    exact (not_lt_of_ge hε) hscore
  refine ⟨lo, N, M, u, hM, hbox, hcost, hne, ?_, hscore⟩
  exact integerResidueBox_lengths_pos _ _ _ _ (fun _ => Nat.cast_pos.mpr hM) hne

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnconditionedTrimmedSliceFamily
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem exists_residue_slice_of_rectangular_scalar_family
    {C Ω I J : Type*} [Fintype C] [Fintype Ω] [Fintype I] [Fintype J]
    (outer : FiniteProbabilityWeights Ω) (source : Ω → Option J × I → ℤ)
    (parent : I → ℤ) (H : I → ℕ)
    (h g : C → (I → ℤ) → ℂ) (epsilon level budget : C → ℝ)
    (D : C → ℕ) (anchor parLo parHi : C → J → ℤ)
    (hpar : ∀ c j, parLo c j < parHi c j) (p : ℝ)
    (htransfer : ∀ c,
      ResidueSliceUpperComparison (h c) (g c) parent H (budget c) (level c)
          (Real.exp (-budget c)) →
      outer.eventProbability (fun z => Real.exp (-p) <
        rectangularScalarDiscrepancy parent H (h c) (g c) (epsilon c) (level c)
          (D c) (anchor c) (parLo c) (parHi c) (hpar c) (source z)) ≤ Real.exp (-p))
    (productive : Ω → Prop)
    (hmass : (Fintype.card C : ℝ) * Real.exp (-p) < outer.eventProbability productive)
    (hproductive : ∀ z, productive z → ∃ c, Real.exp (-p) <
      rectangularScalarDiscrepancy parent H (h c) (g c) (epsilon c) (level c)
        (D c) (anchor c) (parLo c) (parHi c) (hpar c) (source z)) :
    ∃ (c : C) (lo : I → ℤ) (N : I → ℕ) (M : ℕ) (u : I → ℤ),
      0 < M ∧ PhysicalSubbox parent H lo N ∧
      ResidueSliceLogCostLE H lo N M u (budget c) ∧
      Nonempty (IntegerResidueBox lo (fun i => lo i + N i) (fun _ => (M : ℤ)) u) ∧
      (∀ i, 0 < residueIndexLength (lo i) (lo i + N i) M (u i)) ∧
      Real.exp (-budget c) < (physicalResidueMean (h c) lo N M u).re -
        level c * (physicalResidueMean (g c) lo N M u).re := by
  have hfailure : ∃ c, ¬ ResidueSliceUpperComparison (h c) (g c) parent H
      (budget c) (level c) (Real.exp (-budget c)) := by
    by_contra! hn
    have hu := outer.eventProbability_union_bound productive
      (fun c z => Real.exp (-p) <
        rectangularScalarDiscrepancy parent H (h c) (g c) (epsilon c) (level c)
          (D c) (anchor c) (parLo c) (parHi c) (hpar c) (source z)) hproductive
    have hb : outer.eventProbability productive ≤ (Fintype.card C : ℝ) * Real.exp (-p) := by
      apply hu.trans
      calc
        _ ≤ ∑ _c : C, Real.exp (-p) := Finset.sum_le_sum (fun c _ => htransfer c (hn c))
        _ = _ := by simp
    exact (not_lt_of_ge hb) hmass
  obtain ⟨c, hc⟩ := hfailure
  obtain ⟨lo, N, M, u, hM, hbox, hcost, hne, hlength, hscore⟩ :=
    exists_nonempty_residue_slice_of_not_upper (Real.exp_nonneg _) hc
  exact ⟨c, lo, N, M, u, hM, hbox, hcost, hne, hlength, hscore⟩

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

namespace ResidueBoxSlice
variable {J : Type*} [Fintype J] [decJ : DecidableEq J] {N : J → ℕ} {q : ℕ}

theorem scalarParameterEquiv_point (S : ResidueBoxSlice N q)
    (x : ∀ j, Finset.Ico (0 : ℤ) (S.length j : ℤ)) :
    (S.fullSlicePointInIntegerBox (S.scalarParameterEquiv x)).val =
      fun j => (S.start j : ℤ) + (q : ℤ) * (x j).val := by
  funext j
  have hj := (Finset.mem_Ico.mp (x j).property).1
  simp only [fullSlicePointInIntegerBox, point, scalarParameterEquiv,
    Equiv.coe_fn_mk, Nat.cast_add, Nat.cast_mul, Int.toNat_of_nonneg hj]

theorem rectangularScalarDiscrepancy_eq_fullSliceLaw
    {X : Type*} [Fintype X] (S : ResidueBoxSlice N q) (hlen : ∀ j, 0 < S.length j)
    (parent : X → ℤ) (H : X → ℕ) (h g : (X → ℤ) → ℂ)
    (epsilon level : ℝ) (frame : Option J × X → ℤ)
    (hinside : ∀ u : integerBox N,
      smoothAffineSample u.val frame ∈ translatedIntegerBox parent H) :
    rectangularScalarDiscrepancy parent H h g epsilon level q
      (fun j => (S.start j : ℤ)) 0 (fun j => (S.length j : ℤ))
      (fun j => by change (0 : ℤ) < (S.length j : ℤ); exact_mod_cast hlen j) frame =
    (S.fullSliceLaw hlen).mean (fun u =>
      (h (smoothAffineSample u.val frame)).re -
        (1 + epsilon) * level * (g (smoothAffineSample u.val frame)).re) := by
  have hdec : decJ = Classical.decEq J := Subsingleton.elim _ _
  subst decJ
  rw [rectangularScalarDiscrepancy, integerBoxUniformWeights_mean, S.fullSliceLaw_mean]
  apply Fintype.expect_equiv S.scalarParameterEquiv
  intro x
  rw [S.scalarParameterEquiv_point]
  have hi := hinside (S.fullSlicePointInIntegerBox (S.scalarParameterEquiv x))
  rw [S.scalarParameterEquiv_point] at hi
  rw [realZeroExtendFinset_on _ _ hi, realZeroExtendFinset_on _ _ hi]

end ResidueBoxSlice
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RelativeSliceScalarMeshScore
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {J X : Type*} [Fintype J] [decJ : DecidableEq J] [Fintype X]
variable {N : J → ℕ} {q r s d : ℕ}

theorem relativeSlice_scalar_mesh_score
    (original : ResidueBoxSlice N q) (hOriginal : ∀ j, 0 < original.length j)
    (mesh : ResidueBoxSlice N r) (hMesh : ∀ j, 0 < mesh.length j)
    (P : PolynomialPatch X s d) (f : (X → ℤ) → ℝ)
    (parent : X → ℤ) (H : X → ℕ) (frame : Option J × X → ℤ)
    (hinside : ∀ u : integerBox N,
      smoothAffineSample u.val frame ∈ translatedIntegerBox parent H)
    (hf : ∀ x ∈ translatedIntegerBox parent H, f x ∈ Set.Icc (0 : ℝ) 1)
    {τ Λ δ η : ℝ} (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) (hΛ : Λ ∈ Set.Icc (0 : ℝ) 1)
    (hscore : δ ≤ (original.fullSliceLaw hOriginal).mean (fun u =>
      (f (smoothAffineSample u.val frame) - Λ) *
        P.value (fun i => (smoothAffineSample u.val frame i : ℝ))))
    (happrox : ∀ test : integerBox N → ℝ, (∀ u, |test u| ≤ 1) →
      |(original.fullSliceLaw hOriginal).mean test - (mesh.fullSliceLaw hMesh).mean test| ≤ η) :
    δ - η ≤ rectangularScalarDiscrepancy parent H
      (fun x => ((f x * P.value (fun i => (x i : ℝ)) : ℝ) : ℂ))
      (fun x => (P.value (fun i => (x i : ℝ)) : ℂ))
      (relativeScalarPassageSlack τ) ((1 - τ) * Λ) r
      (fun j => (mesh.start j : ℤ)) 0 (fun j => (mesh.length j : ℤ))
      (fun j => by change (0 : ℤ) < (mesh.length j : ℤ); exact_mod_cast hMesh j) frame := by
  have hdec : decJ = Classical.decEq J := Subsingleton.elim _ _
  subst decJ
  rw [mesh.rectangularScalarDiscrepancy_eq_fullSliceLaw hMesh parent H _ _ _ _ frame hinside]
  simp only [Complex.ofReal_re]
  apply relativeScalarPassage_mesh_score (original.fullSliceLaw hOriginal)
    (mesh.fullSliceLaw hMesh) (fun u => f (smoothAffineSample u.val frame))
    (fun u => P.value (fun i => (smoothAffineSample u.val frame i : ℝ)))
    hτ hτhalf hΛ.1 (fun u => (P.value_mem_Icc _).1) hscore
  apply happrox
  intro u
  have hf' := hf _ (hinside u)
  have hg := P.value_mem_Icc (fun i => (smoothAffineSample u.val frame i : ℝ))
  have hdiff : |f (smoothAffineSample u.val frame) - Λ| ≤ 1 :=
    abs_le.mpr ⟨by linarith [hf'.1, hΛ.2], by linarith [hf'.2, hΛ.1]⟩
  rw [abs_mul, abs_of_nonneg hg.1]
  exact (mul_le_mul_of_nonneg_right hdiff hg.1).trans (by simpa using hg.2)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.DenseResidueScalarScoreNet
namespace OAI

section

namespace Erdos3

namespace DenseResidueSliceNetCode

variable {X : Type*} {Q K : ℕ}

theorem realize_spec (N : X → ℕ) (H : ℝ) (M : ℕ)
    (hH : 0 < H) (hN : ∀ i, H ≤ (N i : ℝ)) (hQ : 1 ≤ Q)
    (c : DenseResidueSliceNetCode X Q K) :
    0 < (c.realize N H M).1 ∧ (c.realize N H M).1 ≤ Q ∧
      ∀ i, H / 2 ≤ ((c.realize N H M).2.length i : ℝ) := by
  classical
  let P (z : Σ q, ResidueBoxSlice N q) : Prop :=
    0 < z.1 ∧ z.1 ≤ Q ∧ ∀ i, H / 2 ≤ (z.2.length i : ℝ)
  change P (c.realize N H M)
  unfold realize
  split_ifs with hc
  · exact ⟨hc.1, Nat.le_of_lt_succ c.1.isLt, hc.2.2⟩
  · refine ⟨by norm_num, hQ, ?_⟩
    intro i
    change H / 2 ≤ (N i : ℝ)
    linarith [hN i]

theorem meshCode_valid {N : X → ℕ} {q : ℕ} (S : ResidueBoxSlice N q)
    (hq : 0 < q) (hqQ : q ≤ Q) (M : ℕ) (hM : 0 < M)
    (hlen : ∀ i, 2 * M < S.length i) (hbox : ∀ i, N i ≤ K * M)
    (H : ℝ) (h4 : (4 * M : ℕ) ≤ H) (hH : ∀ i, H ≤ (S.length i : ℝ)) :
    (meshCode S hq hqQ M hM hlen hbox).Valid N H M := by
  refine ⟨hq, ?_, ?_⟩
  · exact (S.meshRounded hq M hM hlen).inside
  · intro i
    change H / 2 ≤ ((S.meshRounded hq M hM hlen).length i : ℝ)
    obtain ⟨offset, _, hcontained, hloss⟩ := S.meshRounded_contained hq M hM hlen
    have hi : S.length i ≤ (S.meshRounded hq M hM hlen).length i + 2 * M := by
      have := hcontained i
      have := hloss i
      omega
    have hiR : (S.length i : ℝ) ≤ (S.meshRounded hq M hM hlen).length i + 2 * (M : ℝ) := by
      exact_mod_cast hi
    have h4R : 4 * (M : ℝ) ≤ H := by exact_mod_cast h4
    linarith [hH i]

theorem realize_meshCode {N : X → ℕ} {q : ℕ} (S : ResidueBoxSlice N q)
    (hq : 0 < q) (hqQ : q ≤ Q) (M : ℕ) (hM : 0 < M)
    (hlen : ∀ i, 2 * M < S.length i) (hbox : ∀ i, N i ≤ K * M)
    (H : ℝ) (h4 : (4 * M : ℕ) ≤ H) (hH : ∀ i, H ≤ (S.length i : ℝ)) :
    (meshCode S hq hqQ M hM hlen hbox).realize N H M =
      ⟨q, S.meshRounded hq M hM hlen⟩ := by
  classical
  rw [realize, dif_pos (meshCode_valid S hq hqQ M hM hlen hbox H h4 hH)]
  rfl

theorem exists_realize_meshRounded {N : X → ℕ} {q : ℕ} (S : ResidueBoxSlice N q)
    (hq : 0 < q) (hqQ : q ≤ Q) (M : ℕ) (hM : 0 < M)
    (hbox : ∀ i, N i ≤ K * M) (H : ℝ) (h4 : (4 * M : ℕ) ≤ H)
    (hH : ∀ i, H ≤ (S.length i : ℝ)) :
    ∃ (hlen : ∀ i, 2 * M < S.length i) (c : DenseResidueSliceNetCode X Q K),
      c.realize N H M = ⟨q, S.meshRounded hq M hM hlen⟩ := by
  have hlen (i : X) : 2 * M < S.length i := by
    have h4R : 4 * (M : ℝ) ≤ H := by exact_mod_cast h4
    have hMR : (0 : ℝ) < M := by exact_mod_cast hM
    have hi : 2 * (M : ℝ) < S.length i := by linarith [hH i]
    exact_mod_cast hi
  exact ⟨hlen, meshCode S hq hqQ M hM hlen hbox,
    realize_meshCode S hq hqQ M hM hlen hbox H h4 hH⟩

end DenseResidueSliceNetCode
end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {X : Type*} [Fintype X] [DecidableEq X] {N : X → ℕ} {q : ℕ}

theorem fullSliceSupport_card (S : ResidueBoxSlice N q) (hq : 0 < q) :
    S.fullSliceSupport.card = ∏ i, S.length i := by
  rw [fullSliceSupport, Finset.card_image_of_injective _
    (fullSlicePointInIntegerBox_injective S hq)]
  simp only [Finset.card_univ, Fintype.card_pi, Fintype.card_fin]

theorem fullSliceSupport_nonempty (S : ResidueBoxSlice N q)
    (hlen : ∀ i, 0 < S.length i) : S.fullSliceSupport.Nonempty := by
  let u : ∀ i, Fin (S.length i) := fun i => ⟨0, hlen i⟩
  exact ⟨S.fullSlicePointInIntegerBox u, Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩⟩

theorem fullSliceLaw_mean_eq_support (S : ResidueBoxSlice N q)
    (hlen : ∀ i, 0 < S.length i) (hq : 0 < q) (f : integerBox N → ℝ) :
    (S.fullSliceLaw hlen).mean f = 𝔼 x ∈ S.fullSliceSupport, f x := by
  rw [fullSliceLaw_mean, fullSliceSupport,
    Finset.expect_image (fullSlicePointInIntegerBox_injective S hq).injOn]

theorem fullSliceSupport_subset (S T : ResidueBoxSlice N q) (offset : X → ℕ)
    (hstart : ∀ i, T.start i = S.start i + q * offset i)
    (hlength : ∀ i, offset i + T.length i ≤ S.length i) :
    T.fullSliceSupport ⊆ S.fullSliceSupport := by
  intro x hx
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx
  let v : ∀ i, Fin (S.length i) := fun i =>
    ⟨offset i + (u i).val, by have := (u i).isLt; have := hlength i; omega⟩
  apply Finset.mem_image.mpr
  refine ⟨v, Finset.mem_univ _, ?_⟩
  apply Subtype.ext
  funext i
  simp only [fullSlicePointInIntegerBox, point, v, hstart, Nat.mul_add, Nat.add_assoc]

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {X : Type*} [Fintype X] [DecidableEq X] {N : X → ℕ} {q : ℕ}

theorem fullSliceLaw_mean_sub_le_of_coordinate_deficit
    (S T : ResidueBoxSlice N q) (hq : 0 < q)
    (hlenS : ∀ i, 0 < S.length i) (hlenT : ∀ i, 0 < T.length i)
    (offset : X → ℕ) (hstart : ∀ i, T.start i = S.start i + q * offset i)
    (hlength : ∀ i, offset i + T.length i ≤ S.length i)
    (η : ℝ) (hdeficit : ∀ i,
      ((S.length i - T.length i : ℕ) : ℝ) / (S.length i : ℝ) ≤ η)
    (f : integerBox N → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    |(S.fullSliceLaw hlenS).mean f - (T.fullSliceLaw hlenT).mean f| ≤
      2 * (Fintype.card X : ℝ) * η := by
  have hsub := fullSliceSupport_subset S T offset hstart hlength
  have hcard := Finset.card_le_card hsub
  have hcardpos : (0 : ℝ) < S.fullSliceSupport.card := by
    exact_mod_cast (fullSliceSupport_nonempty S hlenS).card_pos
  have hside (i) : T.length i ≤ S.length i := by have := hlength i; omega
  have hproduct := denseProductNatCardDeficit_le_card_mul S.length T.length
    hlenS hside η hdeficit
  have hratio : ((S.fullSliceSupport.card - T.fullSliceSupport.card : ℕ) : ℝ) /
      (S.fullSliceSupport.card : ℝ) ≤ (Fintype.card X : ℝ) * η := by
    rw [Nat.cast_sub hcard, sub_div, div_self (ne_of_gt hcardpos)]
    simpa only [fullSliceSupport_card S hq, fullSliceSupport_card T hq] using hproduct
  rw [fullSliceLaw_mean_eq_support S hlenS hq, fullSliceLaw_mean_eq_support T hlenT hq]
  have hmean := abs_expect_parent_sub_subset_le_abs S.fullSliceSupport T.fullSliceSupport
    (fullSliceSupport_nonempty T hlenT) hsub f (fun x _ => hf x)
  exact hmean.trans (by
    simpa only [mul_div_assoc, mul_assoc] using mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 2))

theorem fullSliceLaw_mean_sub_le_of_length_loss
    (S T : ResidueBoxSlice N q) (hq : 0 < q)
    (hlenS : ∀ i, 0 < S.length i) (hlenT : ∀ i, 0 < T.length i)
    (offset : X → ℕ) (hstart : ∀ i, T.start i = S.start i + q * offset i)
    (hlength : ∀ i, offset i + T.length i ≤ S.length i)
    {H M : ℝ} (hH : 0 < H) (hM : 0 ≤ M)
    (hLower : ∀ i, H ≤ (S.length i : ℝ))
    (hLoss : ∀ i, ((S.length i - T.length i : ℕ) : ℝ) ≤ 2 * M)
    (f : integerBox N → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    |(S.fullSliceLaw hlenS).mean f - (T.fullSliceLaw hlenT).mean f| ≤
      4 * (Fintype.card X : ℝ) * M / H := by
  have hdeficit (i) : ((S.length i - T.length i : ℕ) : ℝ) / (S.length i : ℝ) ≤
      2 * M / H := by
    exact (div_le_div_of_nonneg_right (hLoss i) (Nat.cast_nonneg _)).trans
      (div_le_div_of_nonneg_left (by positivity) hH (hLower i))
  have h := fullSliceLaw_mean_sub_le_of_coordinate_deficit S T hq hlenS hlenT
    offset hstart hlength (2 * M / H) hdeficit f hf
  convert h using 1
  ring

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem fullSliceLaw_sigma_congr
    {X : Type*} [Fintype X] [DecidableEq X] {N : X → ℕ}
    (S T : Σ q, ResidueBoxSlice N q) (h : S = T)
    (hS : ∀ i, 0 < S.2.length i) (hT : ∀ i, 0 < T.2.length i) :
    S.2.fullSliceLaw hS = T.2.fullSliceLaw hT := by
  cases h
  rfl

theorem exists_denseResidueSliceLaw_net
    (X : Type*) [Fintype X] [DecidableEq X]
    {δ ε C : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hC : 1 ≤ C) :
    let Q := ⌈2 / δ⌉₊
    let K := denseResidueMeshCap (Fintype.card X) δ ε C
    ∀ L : ℝ, 16 * ((Fintype.card X : ℝ) + 1) / (ε * δ) ≤ L →
    ∀ N : X → ℕ, (∀ i, L ≤ (N i : ℝ) ∧ (N i : ℝ) ≤ C * L) →
    ∃ (stride : DenseResidueSliceNetCode X Q K → ℕ)
      (slices : ∀ c, ResidueBoxSlice N (stride c))
      (hlen : ∀ c i, 0 < (slices c).length i),
      (∀ c, 0 < stride c ∧ stride c ≤ Q) ∧
      (∀ c i, δ * L / 2 ≤ ((slices c).length i : ℝ)) ∧
      ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ 2 / δ →
      ∀ (S : ResidueBoxSlice N q) (hS : ∀ i, 0 < S.length i),
        (∀ i, δ * (N i : ℝ) ≤ (S.length i : ℝ)) →
      ∃ c : DenseResidueSliceNetCode X Q K,
        ∀ (f : integerBox N → ℝ), (∀ x, |f x| ≤ 1) →
          |(S.fullSliceLaw hS).mean f - ((slices c).fullSliceLaw (hlen c)).mean f| ≤ ε / 2 := by
  intro Q K L hL N hN
  have hLpos : 0 < L :=
    (div_pos (by positivity) (mul_pos hε hδ)).trans_le hL
  have hH : 0 < δ * L := mul_pos hδ hLpos
  have hNlower : ∀ i, δ * L ≤ (N i : ℝ) :=
    fun i => (mul_le_of_le_one_left hLpos.le hδ₁).trans (hN i).1
  have hQ : 1 ≤ Q := by
    apply Nat.one_le_iff_ne_zero.mpr
    exact ne_of_gt (Nat.ceil_pos.mpr (div_pos (by norm_num) hδ))
  let M := denseResidueMeshStep (Fintype.card X) δ ε L
  obtain ⟨hM, hcover, herror, htrim, hfour⟩ :=
    denseResidueMesh_budget (Fintype.card X) hδ hε hε₁ hC hL
  have hbox : ∀ i, N i ≤ K * M := by
    intro i
    exact_mod_cast (hN i).2.trans hcover
  have hfour' : ((4 * M : ℕ) : ℝ) ≤ δ * L := by exact_mod_cast hfour
  let family (c : DenseResidueSliceNetCode X Q K) := c.realize N (δ * L) M
  have hspec (c : DenseResidueSliceNetCode X Q K) :=
    c.realize_spec N (δ * L) M hH hNlower hQ
  have hlen (c : DenseResidueSliceNetCode X Q K) (i : X) :
      0 < (family c).2.length i := by
    exact_mod_cast (half_pos hH).trans_le ((hspec c).2.2 i)
  refine ⟨fun c => (family c).1, fun c => (family c).2, hlen,
    (fun c => ⟨(hspec c).1, (hspec c).2.1⟩), (fun c => (hspec c).2.2), ?_⟩
  intro q hq hqbound S hS hdense
  have hqQ : q ≤ Q := by
    exact_mod_cast hqbound.trans (Nat.le_ceil (2 / δ))
  have hSlower : ∀ i, δ * L ≤ (S.length i : ℝ) :=
    fun i => (mul_le_mul_of_nonneg_left (hN i).1 hδ.le).trans (hdense i)
  obtain ⟨hround, c, hc⟩ :=
    DenseResidueSliceNetCode.exists_realize_meshRounded S hq hqQ M hM hbox (δ * L)
      hfour' hSlower
  refine ⟨c, ?_⟩
  intro f hf
  obtain ⟨offset, hstart, hlength, hloss⟩ := S.meshRounded_contained hq M hM hround
  have hcompare := S.fullSliceLaw_mean_sub_le_of_length_loss
    (S.meshRounded hq M hM hround) hq hS (S.meshRounded_length_pos hq M hM hround)
    offset hstart hlength hH (Nat.cast_nonneg M) hSlower
    (fun i => by exact_mod_cast hloss i) f hf
  have herr := hcompare.trans herror
  have hlaw := fullSliceLaw_sigma_congr (family c)
    ⟨q, S.meshRounded hq M hM hround⟩ hc (hlen c)
    (S.meshRounded_length_pos hq M hM hround)
  rw [hlaw]
  exact herr

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem exists_denseResidueScalarScore_net
    (J : Type*) [Fintype J] [DecidableEq J] [Nonempty J]
    {density accuracy ratio : ℝ} (hdensity : 0 < density) (hdensity₁ : density ≤ 1)
    (haccuracy : 0 < accuracy) (haccuracy₁ : accuracy ≤ 1) (hratio : 1 ≤ ratio) :
    let Q := ⌈2 / density⌉₊
    let K := denseResidueMeshCap (Fintype.card J) density accuracy ratio
    ∀ L : ℝ, 16 * ((Fintype.card J : ℝ) + 1) / (accuracy * density) ≤ L →
    ∀ N : J → ℕ, (∀ i, L ≤ (N i : ℝ) ∧ (N i : ℝ) ≤ ratio * L) →
    ∃ (stride : DenseResidueSliceNetCode J Q K → ℕ)
      (slices : ∀ c, ResidueBoxSlice N (stride c))
      (hlen : ∀ c i, 0 < (slices c).length i),
      (∀ c, 0 < stride c ∧ stride c ≤ Q) ∧
      (∀ c i, density * L / 2 ≤ ((slices c).length i : ℝ)) ∧
      ∀ {X : Type*} [Fintype X] {s d : ℕ} (P : PolynomialPatch X s d)
        (f : (X → ℤ) → ℝ) (parent : X → ℤ) (H : X → ℕ)
        (frame : Option J × X → ℤ),
      (∀ u : integerBox N, smoothAffineSample u.val frame ∈ translatedIntegerBox parent H) →
      (∀ x ∈ translatedIntegerBox parent H, f x ∈ Set.Icc (0 : ℝ) 1) →
      ∀ {τ Λ gain : ℝ}, 0 < τ → τ ≤ 1 / 2 → Λ ∈ Set.Icc (0 : ℝ) 1 →
      ∀ (q : ℕ), 0 < q → ∀ (original : ResidueBoxSlice N q)
        (hOriginal : ∀ j, 0 < original.length j),
      (∀ j, density * (N j : ℝ) ≤ original.length j) →
      gain ≤ (original.fullSliceLaw hOriginal).mean (fun u =>
        (f (smoothAffineSample u.val frame) - Λ) *
          P.value (fun i => (smoothAffineSample u.val frame i : ℝ))) →
      ∃ c, gain - accuracy / 2 ≤ rectangularScalarDiscrepancy parent H
        (fun x => ((f x * P.value (fun i => (x i : ℝ)) : ℝ) : ℂ))
        (fun x => (P.value (fun i => (x i : ℝ)) : ℂ))
        (relativeScalarPassageSlack τ) ((1 - τ) * Λ) (stride c)
        (fun j => ((slices c).start j : ℤ)) 0 (fun j => ((slices c).length j : ℤ))
        (fun j => by change (0 : ℤ) < ((slices c).length j : ℤ); exact_mod_cast hlen c j)
        frame := by
  intro Q K L hL N hN
  obtain ⟨stride, slices, hlen, hstride, hlength, hnet⟩ :=
    exists_denseResidueSliceLaw_net J hdensity hdensity₁ haccuracy haccuracy₁ hratio L hL N hN
  refine ⟨stride, slices, hlen, hstride, hlength, ?_⟩
  intro X _ s d P f parent H frame hinside hf τ Λ gain hτ hτhalf hΛ
    q hq original hOriginal hdense hscore
  have hLpos : 0 < L :=
    (div_pos (by positivity) (mul_pos haccuracy hdensity)).trans_le hL
  have hprod := (div_le_iff₀ (mul_pos haccuracy hdensity)).mp hL
  have hacc : L * (accuracy * density) ≤ L * density := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left hdensity.le haccuracy₁) hLpos.le
  have htwo : 2 ≤ density * L := by
    have hn : (0 : ℝ) ≤ Fintype.card J := Nat.cast_nonneg _
    nlinarith
  let j := Classical.choice (inferInstance : Nonempty J)
  have hlenj : 2 ≤ original.length j := by
    exact_mod_cast htwo.trans
      ((mul_le_mul_of_nonneg_left (hN j).1 hdensity.le).trans (hdense j))
  have hqbound : (q : ℝ) ≤ 2 / density :=
    (original.stride_lt_two_div_density hq hlenj hdensity (hdense j)).le
  obtain ⟨c, hc⟩ := hnet q hq hqbound original hOriginal hdense
  exact ⟨c, relativeSlice_scalar_mesh_score original hOriginal (slices c) (hlen c)
    P f parent H frame hinside hf hτ hτhalf hΛ hscore hc⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RelativePhysicalResiduePatch
namespace OAI

section

namespace Erdos3
open scoped BigOperators

variable {X : Type*} [Fintype X] [decX : DecidableEq X]

theorem physicalResidue_reparamPatch_score {s d : ℕ}
    (N H : X → ℕ) (lo a : X → ℤ) (M : ℕ) (hM : 0 < M)
    (hbox : PhysicalSubbox (fun _ => 0) N lo H)
    (hlen : ∀ i, 0 < residueIndexLength (lo i) (lo i + H i) M (a i))
    (f : (X → ℤ) → ℝ) (target : ℝ) (A : PolynomialPatch X s d) :
    let S := ResidueBoxSlice.ofPhysicalResidue N H lo a M hM hbox hlen
    relativePatchSliceScore S f target (S.reparamPatch A) =
      (physicalResidueMean (fun x =>
        (((f x - target) * A.value (fun i => (x i : ℝ)) : ℝ) : ℂ)) lo H M a).re := by
  classical
  have hdec : decX = (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
  subst decX
  intro S
  let e := ResidueBoxSlice.ofPhysicalResidueEquiv N H lo a M hM hbox hlen
  have he (t : ∀ i, Fin (S.length i)) (i : X) :
      (e t i).val = ((S.point t i).val : ℤ) :=
    ResidueBoxSlice.ofPhysicalResidueEquiv_val N H lo a M hM hbox hlen t i
  calc
    _ = 𝔼 t : ∀ i, Fin (S.length i),
        (f (fun i => ((S.point t i).val : ℤ)) - target) *
          A.value (fun i => ((S.point t i).val : ℝ)) := by
      unfold relativePatchSliceScore
      apply Finset.expect_congr rfl
      intro t _
      rw [ResidueBoxSlice.reparamPatch_value]
    _ = 𝔼 x : IntegerResidueBox lo (fun i => lo i + H i) (fun _ => (M : ℤ)) a,
        (f (fun i => (x i).val) - target) *
          A.value (fun i => ((x i).val : ℝ)) := by
      apply Fintype.expect_equiv e
      intro t
      simp only [he, Int.cast_natCast]
    _ = _ := by
      simp only [physicalResidueMean, Finset.expect_eq_sum_div_card,
        ← Complex.ofReal_sum, ← Complex.ofReal_natCast, ← Complex.ofReal_div,
        Complex.ofReal_re]

theorem relativePatchSliceConclusion_of_physicalResidueMean {s d : ℕ}
    (N : X → ℕ) (f : (X → ℤ) → ℝ) (A : PolynomialPatch X s d)
    (lo : X → ℤ) (H : X → ℕ) (M : ℕ) (a : X → ℤ) (target cost : ℝ)
    (hM : 0 < M) (hbox : PhysicalSubbox (fun _ => 0) N lo H)
    (hlen : ∀ i, 0 < residueIndexLength (lo i) (lo i + H i) M (a i))
    (hcost : ResidueSliceLogCostLE N lo H M a cost)
    (hcomplexity : relativePatchComplexity A ≤ cost)
    (hscore : Real.exp (-cost) ≤ (physicalResidueMean (fun x =>
      (((f x - target) * A.value (fun i => (x i : ℝ)) : ℝ) : ℂ)) lo H M a).re) :
    RelativePatchSliceConclusion s N f target d cost := by
  let S := ResidueBoxSlice.ofPhysicalResidue N H lo a M hM hbox hlen
  refine ⟨M, hM, S, d, S.reparamPatch A, hcost, le_rfl, hcomplexity, ?_⟩
  rw [physicalResidue_reparamPatch_score N H lo a M hM hbox hlen f target A]
  exact hscore

theorem relativePatchSliceConclusion_of_nonempty_physicalResidueMean {s d : ℕ}
    (N : X → ℕ) (f : (X → ℤ) → ℝ) (A : PolynomialPatch X s d)
    (lo : X → ℤ) (H : X → ℕ) (M : ℕ) (a : X → ℤ) (target cost : ℝ)
    (hM : 0 < M) (hbox : PhysicalSubbox (fun _ => 0) N lo H)
    (hne : Nonempty (IntegerResidueBox lo (fun i => lo i + H i) (fun _ => (M : ℤ)) a))
    (hcost : ResidueSliceLogCostLE N lo H M a cost)
    (hcomplexity : relativePatchComplexity A ≤ cost)
    (hscore : Real.exp (-cost) ≤ (physicalResidueMean (fun x =>
      (((f x - target) * A.value (fun i => (x i : ℝ)) : ℝ) : ℂ)) lo H M a).re) :
    RelativePatchSliceConclusion s N f target d cost := by
  obtain ⟨x⟩ := hne
  have hlen i : 0 < residueIndexLength (lo i) (lo i + H i) M (a i) := by
    rw [residueIndexLength_eq_card _ _ _ _ (Nat.cast_pos.mpr hM)]
    exact Finset.card_pos.mpr ⟨(x i).val, (x i).property⟩
  exact relativePatchSliceConclusion_of_physicalResidueMean N f A lo H M a target cost
    hM hbox hlen hcost hcomplexity hscore

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RelativeScalarNiltestConclusion
namespace OAI

section

namespace Erdos3
open scoped BigOperators TensorProduct

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem physicalResidueMean_sub_mul_re (h g : (X → ℤ) → ℂ)
    (target : ℝ) (lo : X → ℤ) (H : X → ℕ) (M : ℕ) (a : X → ℤ) :
    (physicalResidueMean (fun x => h x - (target : ℂ) * g x) lo H M a).re =
      (physicalResidueMean h lo H M a).re -
        target * (physicalResidueMean g lo H M a).re := by
  simp only [physicalResidueMean, Finset.expect_sub_distrib, ← Finset.mul_expect,
    Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

theorem physicalResidueMean_scalar_patch_difference {s d : ℕ}
    (f : (X → ℤ) → ℝ) (P : PolynomialPatch X s d)
    (h g : (X → ℤ) → ℂ)
    (hg : ∀ x, g x = (P.value (fun i => (x i : ℝ)) : ℂ))
    (hh : ∀ x, h x = (f x : ℂ) * g x)
    (target : ℝ) (lo : X → ℤ) (H : X → ℕ) (M : ℕ) (a : X → ℤ) :
    (physicalResidueMean h lo H M a).re -
        target * (physicalResidueMean g lo H M a).re =
      (physicalResidueMean (fun x =>
        (((f x - target) * P.value (fun i => (x i : ℝ)) : ℝ) : ℂ)) lo H M a).re := by
  have hpoint : (fun x => h x - (target : ℂ) * g x) =
      (fun x => (((f x - target) * P.value (fun i => (x i : ℝ)) : ℝ) : ℂ)) := by
    funext x
    rw [hh, hg, Complex.ofReal_mul, Complex.ofReal_sub, sub_mul]
  rw [← physicalResidueMean_sub_mul_re, hpoint]

theorem relativePatchSliceConclusion_of_scalar_patch_transfer {s d : ℕ}
    (N : X → ℕ) (f : (X → ℤ) → ℝ) (P : PolynomialPatch X s d)
    (h g : (X → ℤ) → ℂ)
    (hg : ∀ x, g x = (P.value (fun i => (x i : ℝ)) : ℂ))
    (hh : ∀ x, h x = (f x : ℂ) * g x)
    (lo : X → ℤ) (H : X → ℕ) (M : ℕ) (a : X → ℤ) (target cost : ℝ)
    (hM : 0 < M) (hbox : PhysicalSubbox (fun _ => 0) N lo H)
    (hne : Nonempty (IntegerResidueBox lo (fun i => lo i + H i) (fun _ => (M : ℤ)) a))
    (hcost : ResidueSliceLogCostLE N lo H M a cost)
    (hcomplexity : relativePatchComplexity P ≤ cost)
    (hscore : Real.exp (-cost) < (physicalResidueMean h lo H M a).re -
      target * (physicalResidueMean g lo H M a).re) :
    RelativePatchSliceConclusion s N f target d cost := by
  apply relativePatchSliceConclusion_of_nonempty_physicalResidueMean
    N f P lo H M a target cost hM hbox hne hcost hcomplexity
  rw [← physicalResidueMean_scalar_patch_difference f P h g hg hh]
  exact hscore.le

theorem relativePatchSliceConclusion_of_scalarNiltest
    {V : Type*} [LieRing V] [LieAlgebra ℚ V]
    [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
    {s d d₀ : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d₀)
    (N : X → ℕ) (f : (X → ℤ) → ℝ) (P : PolynomialPatch X s d)
    (g : nilmanifold.Niltest (fun _ : X => 1)) (h : (X → ℤ) → ℂ)
    (hg : ∀ x, g.eval x = (P.value (fun i => (x i : ℝ)) : ℂ))
    (hh : ∀ x, h x = (f x : ℂ) * g.eval x)
    (lo : X → ℤ) (H : X → ℕ) (M : ℕ) (a : X → ℤ) (target cost : ℝ)
    (hM : 0 < M) (hbox : PhysicalSubbox (fun _ => 0) N lo H)
    (hne : Nonempty (IntegerResidueBox lo (fun i => lo i + H i) (fun _ => (M : ℤ)) a))
    (hcost : ResidueSliceLogCostLE N lo H M a cost)
    (hcomplexity : relativePatchComplexity P ≤ cost)
    (hscore : Real.exp (-cost) < (physicalResidueMean h lo H M a).re -
      target * (physicalResidueMean g.eval lo H M a).re) :
    RelativePatchSliceConclusion s N f target d cost :=
  relativePatchSliceConclusion_of_scalar_patch_transfer N f P h g.eval hg hh
    lo H M a target cost hM hbox hne hcost hcomplexity hscore

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedZeroLayerScalarPassage
namespace OAI

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical TensorProduct
universe u v w
noncomputable section

attribute [local irreducible] integerBoxUniformWeights selectedJointReference trimmedIntegerBox
  scalarInitialThreshold Fintype.card

theorem exists_indexed_comparable_scalar_retained_slice_patch_s2_oai (s d r : ℕ)
    (hd : 2 ≤ d) (hr : 2 ≤ r) {τ : ℝ} (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) :
    ∃ C F : ℕ, 2 ≤ C ∧ 2 ≤ F ∧
    ∀ {K : Type w} [Fintype K] [DecidableEq K] (_hK : Fintype.card K = d),
    ∀ {I : Type u} {V : Type v} [Fintype I] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d₀ rank : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d₀)
      {p σ Λ density accuracy gain : ℝ},
    2 ≤ p → (Fintype.card I : ℝ) ≤ p →
    0 < σ → σ ≤ 1 → σ⁻¹ ≤ Real.exp p →
    Λ ∈ Set.Icc (0 : ℝ) 1 → Real.exp (-p) ≤ (1 - τ) * Λ →
    0 < density → density ≤ 1 → density⁻¹ ≤ Real.exp p →
    0 < accuracy → accuracy ≤ 1 →
    ∀ (P : PolynomialPatch I s rank) (g : nilmanifold.Niltest (fun _ : I => 1)),
      g.ComplexityLE p → relativePatchComplexity P ≤ p →
      (∀ x, g.eval x = (P.value (fun i => (x i : ℝ)) : ℂ)) →
    let target := 8 * ((r * d : ℕ) + 1 : ℝ) * (p + 1)
    let budget := (target + 2) ^ C
    let L := Real.exp budget
    let Q := ⌈2 / density⌉₊
    let meshCap := denseResidueMeshCap d density accuracy (r : ℝ)
    Real.exp (-target) < gain - accuracy / 2 →
    16 * ((d : ℝ) + 1) / (accuracy * density) ≤ L →
    ∀ parameters : K → ℕ,
      (∀ j, L ≤ (parameters j : ℝ)) → (∀ j, (parameters j : ℝ) ≤ (r : ℝ) * L) →
    ∀ N : I → ℕ, (∀ i, Real.exp ((p + F) ^ F) ≤ (N i : ℝ)) →
    ∀ f : (I → ℤ) → ℝ,
      (∀ x ∈ translatedIntegerBox (0 : I → ℤ) N, f x ∈ Set.Icc (0 : ℝ) 1) →
    let trim := unconditionedSpatialTrimFraction (Fintype.card I) σ
    let Wsite := ∑ j, (parameters j : ℝ)
    let width := trimmedSpatialWidths (K := K) Wsite trim N
    let margin := spatialTrimMargin trim N
    ∃ (hwidth : ∀ z, 0 < width z) (hmargin : ∀ i, 2 * margin i < N i)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0} width z),
    let outer := selectedJointReference (trimmedIntegerBox N margin)
      (trimmedIntegerBox_nonempty N margin hmargin) (fun _ : I => 1) {0} width hwidth hZ
    ∀ retained : (trimmedIntegerBox N margin × rectangularWeightIndices 0 width 1) → Prop,
      (Fintype.card (DenseResidueSliceNetCode K Q meshCap) : ℝ) * Real.exp (-target) <
        outer.eventProbability retained →
      (∀ z, retained z → ∀ u : integerBox parameters,
        smoothAffineSample u.val (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2) ∈
          translatedIntegerBox (0 : I → ℤ) N) →
      (∀ z, retained z → ∃ q, 0 < q ∧ ∃ S : ResidueBoxSlice parameters q,
        ∃ hlen : ∀ j, 0 < S.length j,
        (∀ j, density * (parameters j : ℝ) ≤ (S.length j : ℝ)) ∧
        gain ≤ (S.fullSliceLaw hlen).mean (fun u =>
          (f (smoothAffineSample u.val (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)) - Λ) *
            P.value (fun i => (smoothAffineSample u.val
              (fun k => jointIntegerFrame (z.1.val,z.2.val) k.1 k.2) i : ℝ)))) →
      RelativePatchSliceConclusion s N f ((1 - τ) * Λ) rank ((p + F) ^ F) := by
  obtain ⟨heps, heps1⟩ := relativeScalarPassageSlack_bounds hτ hτhalf
  obtain ⟨_, C, F, _, hC, hF, hscalar⟩ :=
    exists_indexed_comparable_scalar_shared_slice_tail_s2.{u,v,w,w} s d r hd hr heps heps1
  refine ⟨C, F, hC, hF, ?_⟩
  intro K _ decK hK I V _ _ _ _ _ _ _ d₀ rank nilmanifold p σ Λ density accuracy gain hp hn
    hσ hσ1 hσinv hΛ hlevel hdensity hdensity1 hdensityInv haccuracy haccuracy1
    P g hg hP hgval target budget L Q meshCap hgap hmesh parameters hlo hhi N hN f hf
    trim Wsite width margin
  let : Nonempty K := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card K)
  have hnetExists :=
    exists_denseResidueScalarScore_net K hdensity hdensity1 haccuracy haccuracy1
      (show (1 : ℝ) ≤ r by exact_mod_cast (show 1 ≤ r by omega))
      L (by simpa only [hK] using hmesh) parameters (fun j => ⟨hlo j, hhi j⟩)
  rw [hK] at hnetExists
  obtain ⟨stride, slices, hlen, hstride, hlength, hnet⟩ := hnetExists
  have hlevel2 : (1 - τ) * Λ ≤ 2 := by nlinarith [hΛ.1, hΛ.2]
  have hunit (x : I → ℤ) (_hx : x ∈ translatedIntegerBox (0 : I → ℤ) N) :
      (g.eval x).im = 0 ∧ 0 ≤ (g.eval x).re ∧ (g.eval x).re ≤ 1 := by
    rw [hgval]
    exact ⟨Complex.ofReal_im _, by simpa only [Complex.ofReal_re, Set.mem_Icc] using P.value_mem_Icc _⟩
  obtain ⟨hwidth, hmargin, hZ, hparam, hbudgetFinal, htail⟩ :=
    hscalar hK nilmanifold hp hn hσ hσ1 hσinv hlevel hlevel2 hdensity hdensityInv g hg
      parameters hlo hhi stride slices (fun c => (hstride c).1) (fun c => (hstride c).2)
      hlength N hN hunit
  refine ⟨hwidth, hmargin, hZ, ?_⟩
  intro outer retained hmass hinside hretained
  let h : (I → ℤ) → ℂ := fun x => ((f x * P.value (fun i => (x i : ℝ)) : ℝ) : ℂ)
  have hgf : g.eval = fun x => (P.value (fun i => (x i : ℝ)) : ℂ) := funext hgval
  have hh (x : I → ℤ) (hx : x ∈ translatedIntegerBox (0 : I → ℤ) N) :
      0 ≤ (h x).re ∧ (h x).re ≤ 1 := by
    change 0 ≤ f x * P.value _ ∧ f x * P.value _ ≤ 1
    refine ⟨mul_nonneg (hf x hx).1 (P.value_mem_Icc _).1, ?_⟩
    calc
      f x * P.value _ ≤ 1 * P.value _ :=
        mul_le_mul_of_nonneg_right (hf x hx).2 (P.value_mem_Icc _).1
      _ ≤ 1 := by simpa only [one_mul] using (P.value_mem_Icc _).2
  obtain ⟨c, lo, H, M, a, hM, hbox, hcost, hne, _, hscore⟩ :=
    exists_residue_slice_of_rectangular_scalar_family outer
      (fun z i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2) 0 N
      (fun _ => h) (fun _ => g.eval) (fun _ => relativeScalarPassageSlack τ)
      (fun _ => (1 - τ) * Λ) (fun _ => budget) stride
      (fun c j => ((slices c).start j : ℤ)) (fun _ => 0)
      (fun c j => ((slices c).length j : ℤ)) hparam target
      (fun c hupper => by
        have hdec : decK =
            (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
        have ht := htail c h hh hupper
        rw [hdec] at ht
        simpa only [rectangularScalarDiscrepancy, outer, margin, width, Wsite, trim, target, Pi.zero_def]
          using ht)
      retained (by simpa only [hK] using hmass) (by
        intro z hz
        obtain ⟨q, hq, S, hS, hdense, hscore⟩ := hretained z hz
        obtain ⟨c, hc⟩ := hnet P f 0 N
          (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)
          (hinside z hz) hf hτ hτhalf hΛ q hq S hS hdense hscore
        refine ⟨c, hgap.trans_le ?_⟩
        simpa only [h, hgf] using hc)
  have hpTarget : p ≤ target := by
    dsimp [target]
    nlinarith [Nat.cast_nonneg (α := ℝ) (r * d)]
  have htargetBudget : target ≤ budget := by
    have hbase : 1 ≤ target + 2 := by linarith
    have hpow := le_self_pow₀ hbase (by omega : C ≠ 0)
    change target ≤ (target + 2) ^ C
    linarith
  have hresult := relativePatchSliceConclusion_of_scalarNiltest nilmanifold N f P g h hgval
    (fun x => by simp only [h, hgval, Complex.ofReal_mul])
    lo H M a ((1 - τ) * Λ) budget hM hbox hne hcost
    (hP.trans (hpTarget.trans htargetBudget)) hscore
  exact hresult.mono le_rfl hbudgetFinal

end
end Erdos3

end

end OAI
end

theorem solution.{u, v, w} : type_of% @OAI.Erdos3.exists_indexed_comparable_scalar_retained_slice_patch_s2_oai.{u, v, w} := @OAI.Erdos3.exists_indexed_comparable_scalar_retained_slice_patch_s2_oai.{u, v, w}

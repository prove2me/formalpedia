-- Prove2me | solution 1 for OAI.Falconer.Regularization.scalar_dyadic_projection
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T21:57:39.34911+00:00
-- url     : https://prove2.me/submissions/79b19645-168e-43fd-b7d7-ab978cc2dc27

import Mathlib
import Definitions.Def_OAIQ088F002
import Theorems.Thm_OAI_Falconer_Regularization_scalar_weak_block_projection

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarSumCells
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer-cell comparison for scalar sumsets. These constant-factor
bridges allow the finite additive-combinatorial estimates to be applied
at the same scale as the parameter projections. -/
namespace Falconer
open scoped Pointwise

theorem floor_add_carry (u v : ℝ) :
    ⌊u+v⌋ = ⌊u⌋+⌊v⌋ ∨ ⌊u+v⌋ = ⌊u⌋+⌊v⌋+1 := by
  have h1 := Int.le_floor_add u v
  have h2 := Int.le_floor_add_floor u v
  omega

theorem scalarCells_add_subset (δ : ℝ) (A B : Finset ℝ) :
    scalarCells δ (A+B) ⊆ (scalarCells δ A+scalarCells δ B) ∪
      ((scalarCells δ A+scalarCells δ B).image fun z => z+1) := by
  intro z hz
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_add.mp hx
  have hmem : ⌊a/δ⌋+⌊b/δ⌋ ∈ scalarCells δ A+scalarCells δ B :=
    Finset.add_mem_add (Finset.mem_image.mpr ⟨a,ha,rfl⟩) (Finset.mem_image.mpr ⟨b,hb,rfl⟩)
  rw [add_div]
  rcases floor_add_carry (a/δ) (b/δ) with h | h
  · exact Finset.mem_union_left _ (h ▸ hmem)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,hmem,h.symm⟩)

theorem add_scalarCells_subset (δ : ℝ) (A B : Finset ℝ) :
    scalarCells δ A+scalarCells δ B ⊆ scalarCells δ (A+B) ∪
      ((scalarCells δ (A+B)).image fun z => z-1) := by
  intro z hz
  obtain ⟨u,hu,v,hv,rfl⟩ := Finset.mem_add.mp hz
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
  have hmem : ⌊a/δ+b/δ⌋ ∈ scalarCells δ (A+B) := by
    rw [← add_div]
    exact Finset.mem_image.mpr ⟨a+b,Finset.add_mem_add ha hb,rfl⟩
  rcases floor_add_carry (a/δ) (b/δ) with h | h
  · exact Finset.mem_union_left _ (h ▸ hmem)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,hmem,by omega⟩)

theorem scalarCells_add_card (δ : ℝ) (A B : Finset ℝ) :
    (scalarCells δ (A+B)).card ≤ 2*(scalarCells δ A+scalarCells δ B).card := by
  have hb := Finset.card_le_card (scalarCells_add_subset δ A B)
  have hc := Finset.card_union_le (scalarCells δ A+scalarCells δ B)
    ((scalarCells δ A+scalarCells δ B).image fun z => z+1)
  have hi := Finset.card_image_le (s := scalarCells δ A+scalarCells δ B) (f := fun z => z+1)
  omega

theorem add_scalarCells_card (δ : ℝ) (A B : Finset ℝ) :
    (scalarCells δ A+scalarCells δ B).card ≤ 2*(scalarCells δ (A+B)).card := by
  have hb := Finset.card_le_card (add_scalarCells_subset δ A B)
  have hc := Finset.card_union_le (scalarCells δ (A+B))
    ((scalarCells δ (A+B)).image fun z => z-1)
  have hi := Finset.card_image_le (s := scalarCells δ (A+B)) (f := fun z => z-1)
  omega

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarRuzsa
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar discretized Ruzsa triangle inequality, with the rounding
constant stated explicitly. -/
namespace Falconer
open scoped Pointwise

theorem floor_sub_carry (u v : ℝ) :
    ⌊u-v⌋ = ⌊u⌋-⌊v⌋ ∨ ⌊u-v⌋ = ⌊u⌋-⌊v⌋-1 := by
  have h1 := Int.le_floor_add (u-v) v
  have h2 := Int.le_floor_add_floor (u-v) v
  rw [sub_add_cancel] at h1 h2
  omega

theorem scalarCells_sub_subset (δ : ℝ) (A B : Finset ℝ) :
    scalarCells δ (A-B) ⊆ (scalarCells δ A-scalarCells δ B) ∪
      ((scalarCells δ A-scalarCells δ B).image fun z => z-1) := by
  intro z hz
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_sub.mp hx
  have hmem : ⌊a/δ⌋-⌊b/δ⌋ ∈ scalarCells δ A-scalarCells δ B :=
    Finset.sub_mem_sub (Finset.mem_image.mpr ⟨a,ha,rfl⟩) (Finset.mem_image.mpr ⟨b,hb,rfl⟩)
  rw [sub_div]
  rcases floor_sub_carry (a/δ) (b/δ) with h | h
  · exact Finset.mem_union_left _ (h ▸ hmem)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,hmem,h.symm⟩)

theorem scalarCells_sub_card (δ : ℝ) (A B : Finset ℝ) :
    (scalarCells δ (A-B)).card ≤ 2*(scalarCells δ A-scalarCells δ B).card := by
  have hb := Finset.card_le_card (scalarCells_sub_subset δ A B)
  have hc := Finset.card_union_le (scalarCells δ A-scalarCells δ B)
    ((scalarCells δ A-scalarCells δ B).image fun z => z-1)
  have hi := Finset.card_image_le (s := scalarCells δ A-scalarCells δ B) (f := fun z => z-1)
  omega

theorem scalar_ruzsa_triangle (δ : ℝ) (A B C : Finset ℝ) :
    (scalarCells δ (A-C)).card*(scalarCells δ B).card ≤
      8*(scalarCells δ (A+B)).card*(scalarCells δ (C+B)).card := by
  have hR := Finset.ruzsa_triangle_inequality_sub_add_add
    (scalarCells δ A) (scalarCells δ B) (scalarCells δ C)
  calc
    _ ≤ (2*(scalarCells δ A-scalarCells δ C).card)*(scalarCells δ B).card :=
      Nat.mul_le_mul_right _ (scalarCells_sub_card δ A C)
    _ = 2*((scalarCells δ A-scalarCells δ C).card*(scalarCells δ B).card) := by ring
    _ ≤ 2*((scalarCells δ A+scalarCells δ B).card*(scalarCells δ C+scalarCells δ B).card) :=
      Nat.mul_le_mul_left 2 hR
    _ ≤ 2*((2*(scalarCells δ (A+B)).card)*(2*(scalarCells δ (C+B)).card)) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul (add_scalarCells_card δ A B) (add_scalarCells_card δ C B))
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarRepeatedSums
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rounding errors for repeated scalar sumsets. Only one interval of
integer carries is required, so the loss is linear in the number of terms. -/
namespace Falconer
open scoped Pointwise

theorem scalar_nsum_floor (δ : ℝ) (X : Finset ℝ) (n : ℕ)
    {x : ℝ} (hx : x ∈ n • X) :
    ∃ z ∈ n • scalarCells δ X, ∃ k : ℤ,
      0 ≤ k ∧ k ≤ (n : ℤ) ∧ ⌊x/δ⌋ = z+k := by
  classical
  induction n generalizing x with
  | zero =>
    have hx0 : x = 0 := by simpa using hx
    subst x
    exact ⟨0,by simp,0,by norm_num,by norm_num,by simp⟩
  | succ n ih =>
    rw [succ_nsmul] at hx
    obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_add.mp hx
    obtain ⟨z,hz,k,hk0,hkn,hk⟩ := ih ha
    have hbq : ⌊b/δ⌋ ∈ scalarCells δ X := Finset.mem_image.mpr ⟨b,hb,rfl⟩
    have hmem : z+⌊b/δ⌋ ∈ (n+1) • scalarCells δ X := by
      rw [succ_nsmul]
      exact Finset.add_mem_add hz hbq
    rw [add_div]
    rcases floor_add_carry (a/δ) (b/δ) with he | he
    · refine ⟨z+⌊b/δ⌋,hmem,k,hk0,by omega,?_⟩
      omega
    · refine ⟨z+⌊b/δ⌋,hmem,k+1,by omega,by omega,?_⟩
      omega

theorem scalar_signed_sum_cells_subset (δ : ℝ) (X : Finset ℝ) (m n : ℕ) :
    scalarCells δ (m • X-n • X) ⊆
      (m • scalarCells δ X-n • scalarCells δ X)+Finset.Icc (-(n : ℤ)-1) (m : ℤ) := by
  classical
  intro w hw
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_sub.mp hx
  obtain ⟨z,hz,k,hk0,hkm,hk⟩ := scalar_nsum_floor δ X m ha
  obtain ⟨v,hv,l,hl0,hln,hl⟩ := scalar_nsum_floor δ X n hb
  rw [sub_div]
  rcases floor_sub_carry (a/δ) (b/δ) with he | he
  · apply Finset.mem_add.mpr
    exact ⟨z-v,Finset.sub_mem_sub hz hv,k-l,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,by omega⟩
  · apply Finset.mem_add.mpr
    exact ⟨z-v,Finset.sub_mem_sub hz hv,k-l-1,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,by omega⟩

theorem scalar_signed_sum_card (δ : ℝ) (X : Finset ℝ) (m n : ℕ) :
    (scalarCells δ (m • X-n • X)).card ≤
      (m+n+2)*(m • scalarCells δ X-n • scalarCells δ X).card := by
  classical
  have hc : (Finset.Icc (-(n : ℤ)-1) (m : ℤ)).card = m+n+2 := by
    rw [Int.card_Icc]
    omega
  calc
    _ ≤ ((m • scalarCells δ X-n • scalarCells δ X)+Finset.Icc (-(n : ℤ)-1) (m : ℤ)).card :=
      Finset.card_le_card (scalar_signed_sum_cells_subset δ X m n)
    _ ≤ (m • scalarCells δ X-n • scalarCells δ X).card*
        (Finset.Icc (-(n : ℤ)-1) (m : ℤ)).card := Finset.card_add_le
    _ = _ := by rw [hc,Nat.mul_comm]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarPluennecke
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The application form of Pluennecke's inequality for scalar covering
numbers. Its only rounding loss is linear in the number of summands. -/
namespace Falconer
open scoped Pointwise

theorem scalar_pluennecke (δ : ℝ) (A B : Finset ℝ) (hA : A.Nonempty)
    {K : ℝ}
    (hsmall : ((scalarCells δ (A+B)).card : ℝ) ≤ K*(scalarCells δ A).card)
    (m n : ℕ) :
    ((scalarCells δ (m • B-n • B)).card : ℝ) ≤
      (m+n+2)*(2*K)^(m+n)*(scalarCells δ A).card := by
  have hAQ : (scalarCells δ A).Nonempty := Finset.image_nonempty.mpr hA
  have hAc : 0 < ((scalarCells δ A).card : ℝ) :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr hAQ)
  have hR := Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add hAQ
    (scalarCells δ B) m n
  have hRR : ((m • scalarCells δ B-n • scalarCells δ B).card : ℝ) ≤
      (((scalarCells δ A+scalarCells δ B).card : ℝ)/(scalarCells δ A).card)^(m+n)*
        (scalarCells δ A).card := by
    have hReal := NNRat.cast_mono (K := ℝ) hR
    push_cast at hReal
    exact hReal
  have hsum : ((scalarCells δ A+scalarCells δ B).card : ℝ) ≤
      (2*K)*(scalarCells δ A).card := by
    have hc : ((scalarCells δ A+scalarCells δ B).card : ℝ) ≤
        2*((scalarCells δ (A+B)).card : ℝ) := by exact_mod_cast add_scalarCells_card δ A B
    nlinarith
  have hratio : ((scalarCells δ A+scalarCells δ B).card : ℝ)/(scalarCells δ A).card ≤
      2*K := (div_le_iff₀ hAc).2 hsum
  have hpow := pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) hAc.le) hratio (m+n)
  have hbound := hRR.trans (mul_le_mul_of_nonneg_right hpow hAc.le)
  have hcarry : ((scalarCells δ (m • B-n • B)).card : ℝ) ≤
      (m+n+2)*((m • scalarCells δ B-n • scalarCells δ B).card : ℝ) := by
    exact_mod_cast scalar_signed_sum_card δ B m n
  have hmn : (0 : ℝ) ≤ m+n+2 := by positivity
  exact hcarry.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbound hmn)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarCoverCount
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counting cells covered by finitely many translated scalar sets. -/
namespace Falconer
open scoped Pointwise

theorem floor_div_near_nat {δ u v : ℝ} (hδ : 0 < δ) (k : ℕ)
    (huv : |u-v| ≤ k*δ) : |⌊u/δ⌋-⌊v/δ⌋| ≤ (k : ℤ)+1 := by
  have hd : |u/δ-v/δ| ≤ (k : ℝ) := by
    rw [← sub_div,abs_div,abs_of_pos hδ]
    exact (div_le_iff₀ hδ).2 huv
  have hu0 := Int.floor_le (u/δ)
  have hu1 := Int.lt_floor_add_one (u/δ)
  have hv0 := Int.floor_le (v/δ)
  have hv1 := Int.lt_floor_add_one (v/δ)
  have he : |(⌊u/δ⌋ : ℝ)-(⌊v/δ⌋ : ℝ)| ≤ (k : ℝ)+1 := by
    rw [abs_le] at hd ⊢
    constructor <;> linarith
  exact_mod_cast he

theorem scalarCells_near_card_nat {δ : ℝ} (hδ : 0 < δ) (A B : Finset ℝ)
    (k : ℕ) (hcover : ∀ a ∈ A, ∃ b ∈ B, |a-b| ≤ k*δ) :
    (scalarCells δ A).card ≤ (2*k+3)*(scalarCells δ B).card := by
  classical
  let I := fun z : ℤ => Finset.Icc (z-((k : ℤ)+1)) (z+((k : ℤ)+1))
  have hsub : scalarCells δ A ⊆ (scalarCells δ B).biUnion I := by
    intro z hz
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨b,hb,hab⟩ := hcover a ha
    apply Finset.mem_biUnion.mpr
    refine ⟨⌊b/δ⌋,Finset.mem_image.mpr ⟨b,hb,rfl⟩,?_⟩
    have hh := floor_div_near_nat hδ k hab
    rw [abs_le] at hh
    apply Finset.mem_Icc.mpr
    omega
  have hI (z : ℤ) : (I z).card = 2*k+3 := by
    dsimp [I]
    rw [Int.card_Icc]
    omega
  calc
    _ ≤ ((scalarCells δ B).biUnion I).card := Finset.card_le_card hsub
    _ ≤ ∑ z ∈ scalarCells δ B, (I z).card := Finset.card_biUnion_le
    _ = _ := by simp [hI,Nat.mul_comm]

theorem scalarCells_translate_cover {δ : ℝ} (hδ : 0 < δ)
    (P F Z : Finset ℝ) (k : ℕ)
    (hcover : ∀ p ∈ P, ∃ f ∈ F, ∃ z ∈ Z, |p-(f+z)| ≤ k*δ) :
    (scalarCells δ P).card ≤ 2*(2*k+3)*F.card*(scalarCells δ Z).card := by
  classical
  have hn := scalarCells_near_card_nat hδ P (F+Z) k (by
    intro p hp
    obtain ⟨f,hf,z,hz,he⟩ := hcover p hp
    exact ⟨f+z,Finset.add_mem_add hf hz,he⟩)
  have hs := scalarCells_add_card δ F Z
  have hc : (scalarCells δ F+scalarCells δ Z).card ≤ F.card*(scalarCells δ Z).card :=
    Finset.card_add_le.trans (Nat.mul_le_mul_right _ (Finset.card_image_le (s := F)))
  calc
    _ ≤ (2*k+3)*(2*(F.card*(scalarCells δ Z).card)) :=
      hn.trans (Nat.mul_le_mul_left _ (hs.trans (Nat.mul_le_mul_left _ hc)))
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarRuzsaCovering
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ruzsa covering at a fixed scalar resolution, with actual centers
from the original set and an explicit rounding error. -/
namespace Falconer
open scoped Pointwise

theorem scalar_ruzsa_covering {δ K : ℝ} (hδ : 0 < δ)
    (A B : Finset ℝ) (hB : B.Nonempty)
    (hsum : ((scalarCells δ (A+B)).card : ℝ) ≤ K*(scalarCells δ B).card) :
    ∃ F ⊆ A, (F.card : ℝ) ≤ 2*K ∧
      ∀ a ∈ A, ∃ f ∈ F, ∃ b ∈ B, ∃ c ∈ B, |a-(f+(b-c))| ≤ 2*δ := by
  classical
  have hsum' : ((scalarCells δ A+scalarCells δ B).card : ℝ) ≤
      (2*K)*(scalarCells δ B).card := by
    have hc : ((scalarCells δ A+scalarCells δ B).card : ℝ) ≤
        2*((scalarCells δ (A+B)).card : ℝ) := by exact_mod_cast add_scalarCells_card δ A B
    nlinarith
  obtain ⟨D,hDA,hD,hcover⟩ := Finset.ruzsa_covering_add
    (Finset.image_nonempty.mpr hB) hsum'
  let q : ℝ → ℤ := fun x => ⌊x/δ⌋
  let g := Function.invFunOn q (A : Set ℝ)
  have hg (d : ℤ) (hd : d ∈ D) : g d ∈ A ∧ q (g d) = d :=
    Function.invFunOn_pos (Finset.mem_image.mp (hDA hd))
  let F := D.image g
  have hFA : F ⊆ A := by
    rintro f hf
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hf
    exact (hg d hd).1
  have hF : (F.card : ℝ) ≤ 2*K :=
    (Nat.cast_le.mpr (Finset.card_image_le (s := D) (f := g))).trans hD
  refine ⟨F,hFA,hF,?_⟩
  intro a ha
  have hqa : q a ∈ scalarCells δ A := Finset.mem_image.mpr ⟨a,ha,rfl⟩
  obtain ⟨d,hd,z,hz,he⟩ := Finset.mem_add.mp (hcover hqa)
  obtain ⟨u,hu,v,hv,huv⟩ := Finset.mem_sub.mp hz
  obtain ⟨b,hb,hqb⟩ := Finset.mem_image.mp hu
  obtain ⟨c,hc,hqc⟩ := Finset.mem_image.mp hv
  refine ⟨g d,Finset.mem_image.mpr ⟨d,hd,rfl⟩,b,hb,c,hc,?_⟩
  have hqe : q a = q (g d)+q b-q c := by
    rw [(hg d hd).2]
    change q b = u at hqb
    change q c = v at hqc
    rw [hqb,hqc]
    omega
  have hqR : (q a : ℝ) = (q (g d) : ℝ)+(q b : ℝ)-(q c : ℝ) := by exact_mod_cast hqe
  have hqδ := congrArg (fun t : ℝ => t*δ) hqR
  have h0 (x : ℝ) : (q x : ℝ)*δ ≤ x := (le_div_iff₀ hδ).1 (Int.floor_le (x/δ))
  have h1 (x : ℝ) : x < ((q x : ℝ)+1)*δ := (div_lt_iff₀ hδ).1 (Int.lt_floor_add_one (x/δ))
  rw [abs_le]
  constructor <;> linarith [h0 a,h0 (g d),h0 b,h0 c,h1 a,h1 (g d),h1 b,h1 c]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarCoefficientAdd
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Adding two coefficients with small scalar sumsets preserves a
polynomial covering bound. This is an algebraic step in sum-product. -/
namespace Falconer
open scoped Pointwise

theorem scalar_coefficient_add {δ K a b : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (X : Finset ℝ) (hX : X.Nonempty)
    (hdoubling : ((scalarCells δ (X+X)).card : ℝ) ≤ K*(scalarCells δ X).card)
    (ha : ((scalarCells δ (X+X.image (fun x => a*x))).card : ℝ) ≤ K*(scalarCells δ X).card)
    (hb : ((scalarCells δ (X+X.image (fun x => b*x))).card : ℝ) ≤ K*(scalarCells δ X).card) :
    ((scalarCells δ (X+X.image (fun x => (a+b)*x))).card : ℝ) ≤
      19712*K^7*(scalarCells δ X).card := by
  classical
  have ha' : ((scalarCells δ (X.image (fun x => a*x)+X)).card : ℝ) ≤
      K*(scalarCells δ X).card := by rw [add_comm]; exact ha
  have hb' : ((scalarCells δ (X.image (fun x => b*x)+X)).card : ℝ) ≤
      K*(scalarCells δ X).card := by rw [add_comm]; exact hb
  obtain ⟨Fa,_,hFa,hca⟩ := scalar_ruzsa_covering hδ (X.image fun x => a*x) X hX ha'
  obtain ⟨Fb,_,hFb,hcb⟩ := scalar_ruzsa_covering hδ (X.image fun x => b*x) X hX hb'
  let F := Fa+Fb
  let Z := 3 • X-2 • X
  have hcover : ∀ p ∈ X+X.image (fun x => (a+b)*x),
      ∃ f ∈ F, ∃ z ∈ Z, |p-(f+z)| ≤ (4 : ℕ)*δ := by
    intro p hp
    obtain ⟨x,hx,t,ht,rfl⟩ := Finset.mem_add.mp hp
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨fa,hfa,u,hu,v,hv,hea⟩ := hca (a*y) (Finset.mem_image.mpr ⟨y,hy,rfl⟩)
    obtain ⟨fb,hfb,w,hw,z,hz,heb⟩ := hcb (b*y) (Finset.mem_image.mpr ⟨y,hy,rfl⟩)
    have h3 : x+u+w ∈ 3 • X := by
      have hmem := Finset.add_mem_add (Finset.add_mem_add hx hu) hw
      simpa only [show (3 : ℕ) = 2+1 from rfl,add_nsmul,one_nsmul,two_nsmul] using hmem
    have h2 : v+z ∈ 2 • X := by simpa only [two_nsmul] using Finset.add_mem_add hv hz
    refine ⟨fa+fb,Finset.add_mem_add hfa hfb,(x+u+w)-(v+z),Finset.sub_mem_sub h3 h2,?_⟩
    calc
      |x+(a+b)*y-(fa+fb+((x+u+w)-(v+z)))| =
          |(a*y-(fa+(u-v)))+(b*y-(fb+(w-z)))| := by congr 1; ring
      _ ≤ |a*y-(fa+(u-v))|+|b*y-(fb+(w-z))| := abs_add_le _ _
      _ ≤ (4 : ℕ)*δ := by norm_num; linarith
  have hcNat := scalarCells_translate_cover hδ (X+X.image (fun x => (a+b)*x)) F Z 4 hcover
  have hc : ((scalarCells δ (X+X.image (fun x => (a+b)*x))).card : ℝ) ≤
      22*(F.card : ℝ)*(scalarCells δ Z).card := by exact_mod_cast hcNat
  have hFc : (F.card : ℝ) ≤ (Fa.card : ℝ)*(Fb.card : ℝ) := by exact_mod_cast Finset.card_add_le (s := Fa) (t := Fb)
  have hF : (F.card : ℝ) ≤ 4*K^2 := by
    have hh := hFc.trans (mul_le_mul hFa hFb (Nat.cast_nonneg _) (by positivity))
    nlinarith
  have hZ : ((scalarCells δ Z).card : ℝ) ≤ 7*(2*K)^5*(scalarCells δ X).card := by
    have hz := scalar_pluennecke δ X X hX hdoubling 3 2
    norm_num only at hz
    exact hz
  calc
    _ ≤ 22*(F.card : ℝ)*(scalarCells δ Z).card := hc
    _ ≤ (22*(4*K^2))*(7*(2*K)^5*(scalarCells δ X).card) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hF (by norm_num)) hZ
        (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarCoefficientMul
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Multiplying coefficients with small scalar sumsets, with the
rounding cost controlled by an explicit bound for the first coefficient. -/
namespace Falconer
open scoped Pointwise

theorem scalar_coefficient_mul {δ K a b : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (X : Finset ℝ) (hX : X.Nonempty) (M : ℕ) (haM : |a| ≤ M)
    (hdoubling : ((scalarCells δ (X+X)).card : ℝ) ≤ K*(scalarCells δ X).card)
    (ha : ((scalarCells δ (X+X.image (fun x => a*x))).card : ℝ) ≤ K*(scalarCells δ X).card)
    (hb : ((scalarCells δ (X+X.image (fun x => b*x))).card : ℝ) ≤ K*(scalarCells δ X).card) :
    ((scalarCells δ (X+X.image (fun x => (a*b)*x))).card : ℝ) ≤
      (3584*(4*(M : ℝ)+11))*K^8*(scalarCells δ X).card := by
  classical
  have ha' : ((scalarCells δ (X.image (fun x => a*x)+X)).card : ℝ) ≤
      K*(scalarCells δ X).card := by rw [add_comm]; exact ha
  have hb' : ((scalarCells δ (X.image (fun x => b*x)+X)).card : ℝ) ≤
      K*(scalarCells δ X).card := by rw [add_comm]; exact hb
  obtain ⟨Fa,_,hFa,hca⟩ := scalar_ruzsa_covering hδ (X.image fun x => a*x) X hX ha'
  obtain ⟨Fb,_,hFb,hcb⟩ := scalar_ruzsa_covering hδ (X.image fun x => b*x) X hX hb'
  let F := (Fb.image fun f => a*f)+Fa-Fa
  let Z := 3 • X-2 • X
  have hcover : ∀ p ∈ X+X.image (fun x => (a*b)*x),
      ∃ f ∈ F, ∃ z ∈ Z, |p-(f+z)| ≤ (2*M+4 : ℕ)*δ := by
    intro p hp
    obtain ⟨x,hx,t,ht,rfl⟩ := Finset.mem_add.mp hp
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨fb,hfb,u,hu,v,hv,heb⟩ := hcb (b*y) (Finset.mem_image.mpr ⟨y,hy,rfl⟩)
    obtain ⟨f₁,hf₁,u₁,hu₁,v₁,hv₁,he₁⟩ := hca (a*u) (Finset.mem_image.mpr ⟨u,hu,rfl⟩)
    obtain ⟨f₂,hf₂,u₂,hu₂,v₂,hv₂,he₂⟩ := hca (a*v) (Finset.mem_image.mpr ⟨v,hv,rfl⟩)
    have hf : a*fb+f₁-f₂ ∈ F := Finset.sub_mem_sub
      (Finset.add_mem_add (Finset.mem_image.mpr ⟨fb,hfb,rfl⟩) hf₁) hf₂
    have h3 : x+u₁+v₂ ∈ 3 • X := by
      have hm := Finset.add_mem_add (Finset.add_mem_add hx hu₁) hv₂
      simpa only [show (3 : ℕ) = 2+1 from rfl,add_nsmul,one_nsmul,two_nsmul] using hm
    have h2 : v₁+u₂ ∈ 2 • X := by simpa only [two_nsmul] using Finset.add_mem_add hv₁ hu₂
    refine ⟨a*fb+f₁-f₂,hf,(x+u₁+v₂)-(v₁+u₂),Finset.sub_mem_sub h3 h2,?_⟩
    have he₀ : |a*(b*y-(fb+(u-v)))| ≤ 2*(M : ℝ)*δ := by
      rw [abs_mul]
      have hh := mul_le_mul haM heb (abs_nonneg _) (Nat.cast_nonneg M)
      nlinarith
    have htri : |a*(b*y-(fb+(u-v)))+(a*u-(f₁+(u₁-v₁)))-(a*v-(f₂+(u₂-v₂)))| ≤
        |a*(b*y-(fb+(u-v)))|+|a*u-(f₁+(u₁-v₁))|+|a*v-(f₂+(u₂-v₂))| := by
      calc
        _ ≤ |a*(b*y-(fb+(u-v)))+(a*u-(f₁+(u₁-v₁)))|+
            |-(a*v-(f₂+(u₂-v₂)))| := by
          simpa only [sub_eq_add_neg] using abs_add_le
            (a*(b*y-(fb+(u-v)))+(a*u-(f₁+(u₁-v₁)))) (-(a*v-(f₂+(u₂-v₂))))
        _ ≤ _ := by
          rw [abs_neg]
          exact add_le_add (abs_add_le
            (a*(b*y-(fb+(u-v)))) (a*u-(f₁+(u₁-v₁)))) le_rfl
    have heq : x+(a*b)*y-((a*fb+f₁-f₂)+((x+u₁+v₂)-(v₁+u₂))) =
        a*(b*y-(fb+(u-v)))+(a*u-(f₁+(u₁-v₁)))-(a*v-(f₂+(u₂-v₂))) := by ring
    rw [heq]
    push_cast
    linarith
  have hcNat := scalarCells_translate_cover hδ (X+X.image (fun x => (a*b)*x)) F Z (2*M+4) hcover
  have hc : ((scalarCells δ (X+X.image (fun x => (a*b)*x))).card : ℝ) ≤
      (2*(4*(M : ℝ)+11))*(F.card : ℝ)*(scalarCells δ Z).card := by
    have hh : ((scalarCells δ (X+X.image (fun x => (a*b)*x))).card : ℝ) ≤
        2*(2*((2*(M : ℝ))+4)+3)*(F.card : ℝ)*(scalarCells δ Z).card := by exact_mod_cast hcNat
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hFc : (F.card : ℝ) ≤ (Fb.card : ℝ)*(Fa.card : ℝ)*(Fa.card : ℝ) := by
    have hn := (Finset.card_sub_le (s := (Fb.image fun f => a*f)+Fa) (t := Fa)).trans
      (Nat.mul_le_mul_right Fa.card ((Finset.card_add_le (s := Fb.image fun f => a*f) (t := Fa)).trans
        (Nat.mul_le_mul_right Fa.card (Finset.card_image_le (s := Fb)))))
    exact_mod_cast hn
  have hF : (F.card : ℝ) ≤ 8*K^3 := by
    have h1 := mul_le_mul hFb hFa (Nat.cast_nonneg Fa.card) (by positivity : 0 ≤ 2*K)
    have h2 := mul_le_mul h1 hFa (Nat.cast_nonneg Fa.card) (by positivity : 0 ≤ (2*K)*(2*K))
    exact hFc.trans (h2.trans_eq (by ring))
  have hZ : ((scalarCells δ Z).card : ℝ) ≤ 7*(2*K)^5*(scalarCells δ X).card := by
    have hz := scalar_pluennecke δ X X hX hdoubling 3 2
    norm_num only at hz
    exact hz
  calc
    _ ≤ (2*(4*(M : ℝ)+11))*(F.card : ℝ)*(scalarCells δ Z).card := hc
    _ ≤ ((2*(4*(M : ℝ)+11))*(8*K^3))*(7*(2*K)^5*(scalarCells δ X).card) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hF (by positivity)) hZ
        (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarCoefficientNeg
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Negating a coefficient with a small sumset, by the scalar Ruzsa
triangle inequality. -/
namespace Falconer
open scoped Pointwise

theorem scalar_coefficient_neg (δ a : ℝ) {K : ℝ} (hK : 0 ≤ K)
    (X : Finset ℝ) (hX : X.Nonempty)
    (hdoubling : ((scalarCells δ (X+X)).card : ℝ) ≤ K*(scalarCells δ X).card)
    (ha : ((scalarCells δ (X+X.image (fun x => a*x))).card : ℝ) ≤ K*(scalarCells δ X).card) :
    ((scalarCells δ (X+X.image (fun x => (-a)*x))).card : ℝ) ≤
      8*K^2*(scalarCells δ X).card := by
  classical
  have he : X+X.image (fun x => (-a)*x) = X-X.image (fun x => a*x) := by
    ext z
    constructor
    · intro hz
      obtain ⟨x,hx,v,hv,rfl⟩ := Finset.mem_add.mp hz
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_sub.mpr ⟨x,hx,a*y,Finset.mem_image.mpr ⟨y,hy,rfl⟩,by ring⟩
    · intro hz
      obtain ⟨x,hx,v,hv,rfl⟩ := Finset.mem_sub.mp hz
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_add.mpr ⟨x,hx,(-a)*y,Finset.mem_image.mpr ⟨y,hy,rfl⟩,by ring⟩
  rw [he]
  have hR := scalar_ruzsa_triangle δ X X (X.image fun x => a*x)
  have hRR : ((scalarCells δ (X-X.image (fun x => a*x))).card : ℝ)*(scalarCells δ X).card ≤
      8*((scalarCells δ (X+X)).card : ℝ)*(scalarCells δ (X.image (fun x => a*x)+X)).card := by
    exact_mod_cast hR
  have ha' : ((scalarCells δ (X.image (fun x => a*x)+X)).card : ℝ) ≤
      K*(scalarCells δ X).card := by rw [add_comm]; exact ha
  have hprod := mul_le_mul hdoubling ha' (Nat.cast_nonneg _) (mul_nonneg hK (Nat.cast_nonneg _))
  have hAc : 0 < ((scalarCells δ X).card : ℝ) :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr (Finset.image_nonempty.mpr hX))
  apply (mul_le_mul_iff_right₀ hAc).1
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarCoefficientClosure
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite additive and multiplicative closure used in the scalar
sum-product argument. Each stage has an explicit coefficient radius. -/
namespace Falconer
open scoped Pointwise

theorem scalarCoefficientRadius_pos (M n : ℕ) : 0 < scalarCoefficientRadius M n := by
  induction n with
  | zero => simp [scalarCoefficientRadius]
  | succ n ih => simp only [scalarCoefficientRadius]; positivity

theorem scalarCoefficientClosure_bound (S : Finset ℝ) (M : ℕ)
    (hS : ∀ c ∈ S, |c| ≤ M) (n : ℕ) :
    ∀ c ∈ scalarCoefficientClosure S n, |c| ≤ scalarCoefficientRadius M n := by
  induction n with
  | zero =>
    intro c hc
    exact (hS c hc).trans (by simp [scalarCoefficientRadius])
  | succ n ih =>
    intro c hc
    let R : ℝ := scalarCoefficientRadius M n
    have hR : 1 ≤ R := by
      change (1 : ℝ) ≤ (scalarCoefficientRadius M n : ℝ)
      exact_mod_cast Nat.succ_le_of_lt (scalarCoefficientRadius_pos M n)
    have hrad : (scalarCoefficientRadius M (n+1) : ℝ) = 2*R^2 := by
      simp [scalarCoefficientRadius,R]
    rw [hrad]
    have hstep : R ≤ 2*R^2 := by nlinarith
    change c ∈ (scalarCoefficientClosure S n ∪ -scalarCoefficientClosure S n) ∪
      ((scalarCoefficientClosure S n+scalarCoefficientClosure S n) ∪
        (scalarCoefficientClosure S n*scalarCoefficientClosure S n)) at hc
    rcases Finset.mem_union.mp hc with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact (ih c h).trans hstep
      · obtain ⟨x,hx,rfl⟩ := Finset.mem_neg.mp h
        simpa only [abs_neg] using (ih x hx).trans hstep
    · rcases Finset.mem_union.mp h with h | h
      · obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_add.mp h
        have haa := ih a ha
        have hbb := ih b hb
        exact (abs_add_le a b).trans (by change |a| ≤ R at haa; change |b| ≤ R at hbb; nlinarith)
      · obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_mul.mp h
        rw [abs_mul]
        have hh := mul_le_mul (ih a ha) (ih b hb) (abs_nonneg _) (by positivity)
        exact hh.trans (by change R*R ≤ 2*R^2; nlinarith)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarCoefficientBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial losses for finitely many scalar sum-product
operations. No generation or density assertion is assumed here. -/
namespace Falconer

 theorem scalar_coefficient_step_bounds (r : ℕ) {L : ℝ} (hL : 1 ≤ L) :
    let C := 32768*((r : ℝ)+4)
    L ≤ C*L^8 ∧ 19712*L^7 ≤ C*L^8 ∧
      3584*(4*r+11)*L^8 ≤ C*L^8 ∧ 8*L^2 ≤ C*L^8 := by
  dsimp only
  have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg _
  have hC : (19712 : ℝ) ≤ 32768*((r : ℝ)+4) := by nlinarith
  have hC1 : (1 : ℝ) ≤ 32768*((r : ℝ)+4) := by nlinarith
  have hC8 : (8 : ℝ) ≤ 32768*((r : ℝ)+4) := by nlinarith
  have hCm : 3584*(4*(r : ℝ)+11) ≤ 32768*((r : ℝ)+4) := by nlinarith
  have hpow1 : L ≤ L^8 := by simpa using pow_le_pow_right₀ hL (show 1 ≤ (8 : ℕ) by omega)
  have hpow7 := pow_le_pow_right₀ hL (show 7 ≤ (8 : ℕ) by omega)
  have hpow2 := pow_le_pow_right₀ hL (show 2 ≤ (8 : ℕ) by omega)
  refine ⟨hpow1.trans ?_,?_,?_,?_⟩
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right hC1 (pow_nonneg (zero_le_one.trans hL) 8)
  · exact (mul_le_mul_of_nonneg_left hpow7 (by norm_num : (0 : ℝ) ≤ 19712)).trans
      (mul_le_mul_of_nonneg_right hC (by positivity))
  · exact mul_le_mul_of_nonneg_right hCm (by positivity)
  · exact (mul_le_mul_of_nonneg_left hpow2 (by norm_num : (0 : ℝ) ≤ 8)).trans
      (mul_le_mul_of_nonneg_right hC8 (by positivity))

 theorem scalarCoefficientBudget_one_le (M : ℕ) {K : ℝ} (hK : 1 ≤ K) (n : ℕ) :
    1 ≤ scalarCoefficientBudget M K n := by
  induction n with
  | zero => exact hK
  | succ n ih => exact ih.trans (scalar_coefficient_step_bounds (scalarCoefficientRadius M n) ih).1

 theorem scalarCoefficientBudget_zero_le (M : ℕ) {K : ℝ} (hK : 1 ≤ K) (n : ℕ) :
    K ≤ scalarCoefficientBudget M K n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact ih.trans (scalar_coefficient_step_bounds (scalarCoefficientRadius M n)
      (scalarCoefficientBudget_one_le M hK n)).1

 theorem scalarCoefficientBudget_factor (M : ℕ) (K : ℝ) (n : ℕ) :
    scalarCoefficientBudget M K n = scalarCoefficientBudget M 1 n*K^(8^n) := by
  induction n with
  | zero => simp [scalarCoefficientBudget]
  | succ n ih =>
    simp only [scalarCoefficientBudget,ih,mul_pow,← pow_mul,pow_succ]
    ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarClosureProjections
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small scalar projections are preserved through each finite
additive/multiplicative closure stage with the explicit saved budget. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_closure_projections {δ K : ℝ} (hδ : 0 < δ) (hK : 1 ≤ K)
    (X S : Finset ℝ) (hX : X.Nonempty) (M : ℕ)
    (hS : ∀ a ∈ S, |a| ≤ M)
    (hdoubling : ((scalarCells δ (X+X)).card : ℝ) ≤ K*(scalarCells δ X).card)
    (hproj : ∀ a ∈ S,
      ((scalarCells δ (X+X.image (fun x => a*x))).card : ℝ) ≤ K*(scalarCells δ X).card)
    (n : ℕ) :
    ∀ a ∈ scalarCoefficientClosure S n,
      ((scalarCells δ (X+X.image (fun x => a*x))).card : ℝ) ≤
        scalarCoefficientBudget M K n*(scalarCells δ X).card := by
  induction n with
  | zero => exact hproj
  | succ n ih =>
    intro a ha
    let L := scalarCoefficientBudget M K n
    let r := scalarCoefficientRadius M n
    have hL : 1 ≤ L := scalarCoefficientBudget_one_le M hK n
    have hD : ((scalarCells δ (X+X)).card : ℝ) ≤ L*(scalarCells δ X).card :=
      hdoubling.trans (mul_le_mul_of_nonneg_right (scalarCoefficientBudget_zero_le M hK n)
        (Nat.cast_nonneg _))
    have hstep := scalar_coefficient_step_bounds r hL
    change a ∈ (scalarCoefficientClosure S n ∪ -scalarCoefficientClosure S n) ∪
      ((scalarCoefficientClosure S n+scalarCoefficientClosure S n) ∪
        (scalarCoefficientClosure S n*scalarCoefficientClosure S n)) at ha
    change ((scalarCells δ (X+X.image (fun x => a*x))).card : ℝ) ≤
      (32768*((r : ℝ)+4)*L^8)*(scalarCells δ X).card
    rcases Finset.mem_union.mp ha with ha | ha
    · rcases Finset.mem_union.mp ha with ha | ha
      · exact (ih a ha).trans (mul_le_mul_of_nonneg_right hstep.1 (Nat.cast_nonneg _))
      · obtain ⟨b,hb,rfl⟩ := Finset.mem_neg.mp ha
        exact (scalar_coefficient_neg δ b (zero_le_one.trans hL) X hX hD (ih b hb)).trans
          (mul_le_mul_of_nonneg_right hstep.2.2.2 (Nat.cast_nonneg _))
    · rcases Finset.mem_union.mp ha with ha | ha
      · obtain ⟨b,hb,c,hc,rfl⟩ := Finset.mem_add.mp ha
        exact (scalar_coefficient_add hδ (zero_le_one.trans hL) X hX hD (ih b hb) (ih c hc)).trans
          (mul_le_mul_of_nonneg_right hstep.2.1 (Nat.cast_nonneg _))
      · obtain ⟨b,hb,c,hc,rfl⟩ := Finset.mem_mul.mp ha
        exact (scalar_coefficient_mul hδ (zero_le_one.trans hL) X hX r
          (scalarCoefficientClosure_bound S M hS n b hb) hD (ih b hb) (ih c hc)).trans
          (mul_le_mul_of_nonneg_right hstep.2.2.1 (Nat.cast_nonneg _))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarNetIteration
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Repeated finite sum-product amplification of a power-scale interval
net, with its exact error recurrence. -/
namespace Falconer
open scoped Pointwise

 theorem scalarCoefficientClosure_step (S : Finset ℝ) (n : ℕ) :
    scalarCoefficientClosure S n ⊆ scalarCoefficientClosure S (n+1) := by
  intro x hx
  exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarEnergyRefinement
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer the integer additive-energy refinement to separated real
sets, preserving the original points and the quantized difference bound. -/
namespace Falconer
open scoped Pointwise

theorem same_scalar_cell_dist_lt {δ x y : ℝ} (hδ : 0 < δ) (hcell : ⌊x/δ⌋ = ⌊y/δ⌋) :
    |x-y| < δ := by
  have hx0 := Int.floor_le (x/δ)
  have hx1 := Int.lt_floor_add_one (x/δ)
  have hy0 := Int.floor_le (y/δ)
  have hy1 := Int.lt_floor_add_one (y/δ)
  rw [hcell] at hx0 hx1
  have hh : |x/δ-y/δ| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  rw [← sub_div,abs_div,abs_of_pos hδ] at hh
  exact (div_lt_one hδ).1 hh

theorem scalarCells_injective {δ : ℝ} (hδ : 0 < δ) {A : Finset ℝ}
    (hsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ |x-y|) :
    Set.InjOn (fun x => ⌊x/δ⌋) (A : Set ℝ) := by
  intro x hx y hy he
  by_contra hne
  exact (not_lt_of_ge (hsep x hx y hy hne)) (same_scalar_cell_dist_lt hδ he)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarDilationBound
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar dilation changes a fixed-resolution covering number by at
most a linear factor in the dilation bound. -/
namespace Falconer
open scoped Pointwise

theorem scalar_dilation_cells {δ c : ℝ} (hδ : 0 < δ) (A : Finset ℝ)
    (M : ℕ) (hc : |c| ≤ M) :
    (scalarCells δ (A.image fun x => c*x)).card ≤ (2*M+3)*(scalarCells δ A).card := by
  classical
  let q : ℝ → ℤ := fun x => ⌊x/δ⌋
  let g := Function.invFunOn q (A : Set ℝ)
  let F := (scalarCells δ A).image g
  have hF : F.card ≤ (scalarCells δ A).card := Finset.card_image_le
  have hcover : ∀ x ∈ A.image (fun x => c*x),
      ∃ y ∈ F.image (fun x => c*x), |x-y| ≤ (M : ℝ)*δ := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    have hq := Function.invFunOn_pos (f := q) (s := (A : Set ℝ)) ⟨x,hx,rfl⟩
    have hxg : |x-g (q x)| ≤ δ := (same_scalar_cell_dist_lt hδ hq.2.symm).le
    have hgf : g (q x) ∈ F := Finset.mem_image.mpr
      ⟨q x,Finset.mem_image.mpr ⟨x,hx,rfl⟩,rfl⟩
    refine ⟨c*g (q x),Finset.mem_image.mpr ⟨g (q x),hgf,rfl⟩,?_⟩
    rw [← mul_sub,abs_mul]
    exact mul_le_mul hc hxg (abs_nonneg _) (Nat.cast_nonneg M)
  have hn := scalarCells_near_card_nat hδ (A.image fun x => c*x) (F.image fun x => c*x) M hcover
  have hsmall : (scalarCells δ (F.image fun x => c*x)).card ≤ (scalarCells δ A).card :=
    Finset.card_image_le.trans (Finset.card_image_le.trans hF)
  exact hn.trans (Nat.mul_le_mul_left _ hsmall)

theorem scalar_inverse_coefficient_cells {δ a : ℝ} (hδ : 0 < δ) (ha : a ≠ 0)
    (X : Finset ℝ) (M : ℕ) (hM : |a⁻¹| ≤ M) :
    (scalarCells δ (X+X.image (fun x => a⁻¹*x))).card ≤
      (2*M+3)*(scalarCells δ (X+X.image (fun x => a*x))).card := by
  classical
  have he : X+X.image (fun x => a⁻¹*x) =
      (X+X.image (fun x => a*x)).image (fun x => a⁻¹*x) := by
    ext z
    constructor
    · intro hz
      obtain ⟨x,hx,v,hv,rfl⟩ := Finset.mem_add.mp hz
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
      refine Finset.mem_image.mpr ⟨y+a*x,Finset.add_mem_add hy
        (Finset.mem_image.mpr ⟨x,hx,rfl⟩),?_⟩
      simp only [mul_add,← mul_assoc,inv_mul_cancel₀ ha,one_mul,add_comm]
    · intro hz
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨x,hx,w,hw,rfl⟩ := Finset.mem_add.mp hv
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hw
      have heq : a⁻¹*(x+a*y) = y+a⁻¹*x := by
        simp only [mul_add,← mul_assoc,inv_mul_cancel₀ ha,one_mul,add_comm]
      rw [heq]
      exact Finset.add_mem_add hy (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
  rw [he]
  exact scalar_dilation_cells hδ _ M hM

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarBallCandidates
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite critical radii for maximizing scalar local density. -/
namespace Falconer

 theorem scalarBallCandidates_nonempty (δ : ℝ) {E : Finset ℝ} (hE : E.Nonempty) :
    (scalarBallCandidates δ E).Nonempty := by
  obtain ⟨x,hx⟩ := hE
  exact ⟨(x,2),Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x,hx,rfl⟩)⟩

 theorem scalarBallCandidate_bounds {δ : ℝ} (hδ : δ ≤ 1) (E : Finset ℝ)
    (hE : ∀ x ∈ E, |x| ≤ 1) {p : ℝ × ℝ} (hp : p ∈ scalarBallCandidates δ E) :
    p.1 ∈ E ∧ δ ≤ p.2 ∧ p.2 ≤ 2 := by
  rcases Finset.mem_union.mp hp with hp | hp
  · obtain ⟨⟨x,y⟩,hxy,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
    refine ⟨hx,le_max_left _ _,max_le (hδ.trans (by norm_num)) ?_⟩
    exact (abs_sub y x).trans (by linarith [hE y hy,hE x hx])
  · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
    exact ⟨hx,hδ.trans (by norm_num),le_rfl⟩

 theorem scalarBallMass_nonneg (E : Finset ℝ) (u r : ℝ) : 0 ≤ scalarBallMass E u r :=
  Nat.cast_nonneg _

 theorem scalarBallMass_at_two (E : Finset ℝ) (hE : ∀ x ∈ E, |x| ≤ 1)
    {x : ℝ} (hx : x ∈ E) : scalarBallMass E x 2 = (E.card : ℝ) := by
  have he : E.filter (fun y => |y-x| ≤ 2) = E := by
    apply Finset.filter_eq_self.mpr
    intro y hy
    exact (abs_sub y x).trans (by linarith [hE y hy,hE x hx])
  unfold scalarBallMass
  rw [he]

 theorem scalarBallMass_majorized_candidate {δ u r : ℝ} (hδ : 0 < δ) (hdr : δ ≤ r)
    (E : Finset ℝ) (hball : (E.filter fun x => |x-u| ≤ r).Nonempty) :
    ∃ p ∈ scalarBallCandidates δ E, p.2 ≤ 2*r ∧
      scalarBallMass E u r ≤ scalarBallMass E p.1 p.2 := by
  classical
  let F := E.filter fun x => |x-u| ≤ r
  obtain ⟨x,hx⟩ := hball
  obtain ⟨y,hy,hmax⟩ := F.exists_max_image (fun y => |y-x|) ⟨x,hx⟩
  have hxE := (Finset.mem_filter.mp hx).1
  have hyE := (Finset.mem_filter.mp hy).1
  have hrad : max δ |y-x| ≤ 2*r := by
    apply max_le
    · linarith
    · calc
        |y-x| ≤ |y-u|+|u-x| := abs_sub_le y u x
        _ ≤ r+r := add_le_add (Finset.mem_filter.mp hy).2
          (by simpa only [abs_sub_comm] using (Finset.mem_filter.mp hx).2)
        _ = _ := by ring
  refine ⟨(x,max δ |y-x|),Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨(x,y),Finset.mem_product.mpr ⟨hxE,hyE⟩,rfl⟩),hrad,?_⟩
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro z hz
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,
    (hmax z hz).trans (le_max_right _ _)⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarZoom
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite scalar zooming and its ball-count identity. -/
namespace Falconer

 theorem scalarZoom_injective {z R : ℝ} (hR : R ≠ 0) :
    Function.Injective (fun x : ℝ => (x-z)/R) := by
  intro x y h
  have hh := congrArg (fun t : ℝ => t*R) h
  simp only [div_mul_cancel₀ _ hR] at hh
  linarith

 theorem scalarZoom_card {z R : ℝ} (hR : R ≠ 0) (E : Finset ℝ) :
    (scalarZoom z R E).card = E.card :=
  Finset.card_image_of_injective _ (scalarZoom_injective hR)

 theorem scalarZoom_ball_iff {z R u r x : ℝ} (hR : 0 < R) :
    |(x-z)/R-u| ≤ r ↔ |x-(z+R*u)| ≤ R*r := by
  have he : (x-z)/R-u = (x-(z+R*u))/R := by field_simp; ring
  rw [he,abs_div,abs_of_pos hR,div_le_iff₀ hR]
  rw [mul_comm r R]

 theorem scalarZoom_ball_mass {z R : ℝ} (hR : 0 < R) (E : Finset ℝ) (u r : ℝ) :
    scalarBallMass (scalarZoom z R E) u r = scalarBallMass E (z+R*u) (R*r) := by
  classical
  have he : (scalarZoom z R E).filter (fun x => |x-u| ≤ r) =
      (E.filter fun x => |x-(z+R*u)| ≤ R*r).image (fun x => (x-z)/R) := by
    ext y
    constructor
    · intro hy
      obtain ⟨hyE,hyB⟩ := Finset.mem_filter.mp hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hyE
      exact Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,(scalarZoom_ball_iff hR).1 hyB⟩,rfl⟩
    · intro hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨hxE,hxB⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x,hxE,rfl⟩,(scalarZoom_ball_iff hR).2 hxB⟩
  unfold scalarBallMass
  rw [he,Finset.card_image_of_injective _ (scalarZoom_injective hR.ne')]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_ScalarDensitySelection
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selecting a maximal-density interval gives uniform local ball
bounds without any continuum optimization. -/
namespace Falconer

 theorem scalar_maximal_density_interval_candidate {δ κ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hκ : 0 ≤ κ) (E : Finset ℝ) (hE : E.Nonempty) (hbound : ∀ x ∈ E, |x| ≤ 1) :
    ∃ z ∈ E, ∃ R : ℝ, δ ≤ R ∧ R ≤ 2 ∧ (z,R) ∈ scalarBallCandidates δ E ∧
      (E.filter fun x => |x-z| ≤ R).Nonempty ∧
      (E.card : ℝ)/2^κ ≤ scalarBallMass E z R/R^κ ∧
      ∀ u r : ℝ, δ ≤ r → scalarBallMass E u r ≤
        2^κ*(r/R)^κ*scalarBallMass E z R := by
  classical
  let f := fun p : ℝ × ℝ => scalarBallMass E p.1 p.2/p.2^κ
  obtain ⟨p,hp,hmax⟩ := (scalarBallCandidates δ E).exists_max_image f
    (scalarBallCandidates_nonempty δ hE)
  obtain ⟨hz,hRδ,hR2⟩ := scalarBallCandidate_bounds hδ1 E hbound hp
  have hR : 0 < p.2 := hδ.trans_le hRδ
  have hne : (E.filter fun x => |x-p.1| ≤ p.2).Nonempty := by
    refine ⟨p.1,Finset.mem_filter.mpr ⟨hz,?_⟩⟩
    simpa only [sub_self,abs_zero] using hR.le
  refine ⟨p.1,hz,p.2,hRδ,hR2,hp,hne,?_,?_⟩
  · obtain ⟨x,hx⟩ := hE
    have hh := hmax (x,2) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x,hx,rfl⟩))
    simpa only [f,scalarBallMass_at_two E hbound hx] using hh
  · intro u r hdr
    have hr : 0 < r := hδ.trans_le hdr
    by_cases hnonempty : (E.filter fun x => |x-u| ≤ r).Nonempty
    · obtain ⟨q,hq,hqr,hcount⟩ := scalarBallMass_majorized_candidate hδ hdr E hnonempty
      have hqR : 0 < q.2 := hδ.trans_le (scalarBallCandidate_bounds hδ1 E hbound hq).2.1
      have hqmax := hmax q hq
      change scalarBallMass E q.1 q.2/q.2^κ ≤ scalarBallMass E p.1 p.2/p.2^κ at hqmax
      have hqcount : scalarBallMass E q.1 q.2 ≤
          (scalarBallMass E p.1 p.2/p.2^κ)*q.2^κ :=
        (div_le_iff₀ (Real.rpow_pos_of_pos hqR κ)).1 hqmax
      have hp0 : 0 ≤ scalarBallMass E p.1 p.2/p.2^κ := by
        exact div_nonneg (scalarBallMass_nonneg E _ _) (Real.rpow_nonneg hR.le _)
      calc
        _ ≤ scalarBallMass E q.1 q.2 := hcount
        _ ≤ (scalarBallMass E p.1 p.2/p.2^κ)*q.2^κ := hqcount
        _ ≤ (scalarBallMass E p.1 p.2/p.2^κ)*(2*r)^κ :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hqR.le hqr hκ) hp0
        _ = _ := by
          rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hr.le,
            Real.div_rpow hr.le hR.le]
          ring
    · have he : scalarBallMass E u r = 0 := by
        unfold scalarBallMass
        rw [Finset.not_nonempty_iff_eq_empty.mp hnonempty]
        simp
      rw [he]
      have hm := scalarBallMass_nonneg E p.1 p.2
      positivity

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_ScalarDensityRadius
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Original weak ball bounds prevent the maximal-density interval from
collapsing to an uncontrolled radius. -/
namespace Falconer

 theorem scalar_density_radius_inequality {R θ K N m : ℝ}
    (hR : 0 < R) (hθ : 0 ≤ θ) (hK : 1 ≤ K) (hN : 0 < N)
    (hlower : N/(2:ℝ)^θ ≤ m/R^θ)
    (hupper : R ≤ 1 → m ≤ K*R^(2*θ)*N) :
    1 ≤ (2:ℝ)^θ*K*R^θ := by
  by_cases hR1 : R ≤ 1
  · have hp : 0 < R^θ := Real.rpow_pos_of_pos hR θ
    have htwo : 0 < (2:ℝ)^θ := by positivity
    have hl := (le_div_iff₀ hp).1 hlower
    have hl' := mul_le_mul_of_nonneg_left hl htwo.le
    have he : R^(2*θ) = (R^θ)^2 := by
      rw [show 2*θ = θ+θ by ring,Real.rpow_add hR,pow_two]
    have hu := hupper hR1
    rw [he] at hu
    have hu' := mul_le_mul_of_nonneg_left hu htwo.le
    have hlow : N*R^θ ≤ (2:ℝ)^θ*m := by
      have heq : (2:ℝ)^θ*(N/(2:ℝ)^θ*R^θ) = N*R^θ := by field_simp
      rwa [heq] at hl'
    have hh := hlow.trans hu'
    apply (mul_le_mul_iff_left₀ (mul_pos hN hp)).1
    first | (convert hh using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hh.trans (le_of_eq (by ring)))
  · have hp : 1 ≤ R^θ := Real.one_le_rpow (le_of_not_ge hR1) hθ
    have ht : 1 ≤ (2:ℝ)^θ := Real.one_le_rpow (by norm_num) hθ
    have hh : 1 ≤ (2:ℝ)^θ*K := by nlinarith
    nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_ScalarSubsetMass
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative ball bounds and projection covers under the actual scalar
 pruning. The sole cost is the ratio of the numbers of retained leaves. -/
namespace Falconer
open scoped Pointwise

 theorem scalarBallMass_mono {A B : Finset ℝ} (h : A ⊆ B) (u r : ℝ) :
    scalarBallMass A u r ≤ scalarBallMass B u r := by
  unfold scalarBallMass
  exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ h)

namespace Regularization

 theorem scalar_leaf_center_card {N : ℕ} (Q : Finset (CellPath 1))
    (hQ : Q ⊆ cubePaths 1 N) : (Q.image scalarPathCenter).card = Q.card := by
  exact Finset.card_image_of_injOn (scalarPathCenter_injOn Q
    (fun q hq => (mem_cubePaths 1 N q).mp (hQ hq)))

end Regularization
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_ScalarDensityMassControl
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A density interval chosen with half the original Frostman exponent
 retains enough mass even below the rescaled original resolution. -/
namespace Falconer

 theorem scalar_density_relative_mass {R κ K N m : ℝ}
    (hR : 0 < R) (hκ : 0 ≤ κ) (hK : 1 ≤ K) (hN : 0 < N)
    (hmax : N/(2:ℝ)^κ ≤ m/R^κ)
    (hupper : R ≤ 1 → m ≤ K*R^(2*κ)*N) :
    N ≤ (4:ℝ)^κ*K*m := by
  have hr := scalar_density_radius_inequality hR hκ hK hN hmax hupper
  have ht : 0 < (2:ℝ)^κ := by positivity
  have hlow : N*R^κ ≤ (2:ℝ)^κ*m := by
    have hh := (le_div_iff₀ (Real.rpow_pos_of_pos hR κ)).1 hmax
    have hh' := mul_le_mul_of_nonneg_left hh ht.le
    have he : (2:ℝ)^κ*(N/(2:ℝ)^κ*R^κ) = N*R^κ := by field_simp
    nlinarith [he]
  have h1 := mul_le_mul_of_nonneg_right hr hN.le
  have h2 := mul_le_mul_of_nonneg_left hlow
    (mul_nonneg ht.le (show 0 ≤ K by linarith))
  have he : (4:ℝ)^κ = ((2:ℝ)^κ)^2 := by
    rw [show (4:ℝ) = 2*2 by norm_num,Real.mul_rpow (by norm_num) (by norm_num),pow_two]
  rw [he]
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_ScalarPositiveZoom
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The density zoom placed inside the positive coefficient interval. -/
namespace Falconer

 theorem scalar_positive_zoom_bounds {z R : ℝ} (hR : 0 < R) (E : Finset ℝ)
    (hE : ∀ x ∈ E, |x-z| ≤ R) :
    ∀ t ∈ scalarZoom (z-3*R) (6*R) E, 1/3 ≤ t ∧ t ≤ 1 := by
  intro t ht
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
  have hb := (abs_le.mp (hE x hx))
  constructor
  · apply (le_div_iff₀ (by positivity : 0 < 6*R)).2
    linarith
  · apply (div_le_iff₀ (by positivity : 0 < 6*R)).2
    linarith

 theorem scalar_positive_zoom_local_mass {δ κ z R : ℝ} (hδ : 0 < δ) (hR : 0 < R)
    (E : Finset ℝ)
    (hlocal : ∀ u r : ℝ, δ ≤ r → scalarBallMass E u r ≤
      2^κ*(r/R)^κ*scalarBallMass E z R)
    (F : Finset ℝ) (hFE : F ⊆ E) (hF : scalarBallMass E z R = (F.card:ℝ)) :
    ∀ u r : ℝ, δ ≤ 6*R*r →
      scalarBallMass (scalarZoom (z-3*R) (6*R) F) u r ≤
        (12:ℝ)^κ*r^κ*((scalarZoom (z-3*R) (6*R) F).card:ℝ) := by
  intro u r hr
  have hr0 : 0 ≤ r := by nlinarith
  rw [scalarZoom_ball_mass (by positivity),scalarZoom_card (by positivity)]
  have hh := (scalarBallMass_mono hFE (z-3*R+6*R*u) (6*R*r)).trans
    (hlocal (z-3*R+6*R*u) (6*R*r) hr)
  rw [hF,show 6*R*r/R = 6*r by field_simp,Real.mul_rpow (by norm_num) hr0] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  rw [show (12:ℝ) = 2*6 by norm_num,Real.mul_rpow (by norm_num) (by norm_num)]
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_ScalarSmallZoomMass
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balls below the rescaled original resolution remain controlled by
 the exponent reserve in the original coefficient Frostman estimate. -/
namespace Falconer

 theorem scalarBallMass_radius_mono (E : Finset ℝ) (u : ℝ) {r s : ℝ} (h : r ≤ s) :
    scalarBallMass E u r ≤ scalarBallMass E u s := by
  unfold scalarBallMass
  have hs : E.filter (fun x => |x-u| ≤ r) ⊆ E.filter (fun x => |x-u| ≤ s) := by
    intro x hx
    obtain ⟨hxE,hxr⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hxE,hxr.trans h⟩
  exact_mod_cast Finset.card_le_card hs

 theorem scalar_positive_zoom_small_mass {δ κ K z R : ℝ}
    (hδ : 0 < δ) (hκ : 0 ≤ κ) (hK : 0 ≤ K) (hR : 0 < R)
    (E F : Finset ℝ) (hFE : F ⊆ E)
    (hsize : (E.card:ℝ) ≤ (4:ℝ)^κ*K*(F.card:ℝ))
    (hweak : ∀ u : ℝ, scalarBallMass E u δ ≤ K*δ^(2*κ)*(E.card:ℝ))
    (hbudget : K^2*δ^κ ≤ 1) (u r : ℝ) (hr : δ ≤ r) (hsmall : 6*R*r ≤ δ) :
    scalarBallMass (scalarZoom (z-3*R) (6*R) F) u r ≤
      (12:ℝ)^κ*r^κ*((scalarZoom (z-3*R) (6*R) F).card:ℝ) := by
  rw [scalarZoom_ball_mass (by positivity),scalarZoom_card (by positivity)]
  have hp : δ^(2*κ) = (δ^κ)^2 := by
    rw [show 2*κ = κ+κ by ring,Real.rpow_add hδ,pow_two]
  have hδpow : 0 ≤ δ^κ := Real.rpow_nonneg hδ.le _
  have hpow : δ^κ ≤ r^κ := Real.rpow_le_rpow hδ.le hr hκ
  have hbase : (4:ℝ)^κ ≤ (12:ℝ)^κ := Real.rpow_le_rpow (by norm_num) (by norm_num) hκ
  calc
    _ ≤ scalarBallMass E (z-3*R+6*R*u) (6*R*r) := scalarBallMass_mono hFE _ _
    _ ≤ scalarBallMass E (z-3*R+6*R*u) δ := scalarBallMass_radius_mono E _ hsmall
    _ ≤ K*δ^(2*κ)*(E.card:ℝ) := hweak _
    _ ≤ K*δ^(2*κ)*((4:ℝ)^κ*K*(F.card:ℝ)) :=
      mul_le_mul_of_nonneg_left hsize (mul_nonneg hK (Real.rpow_nonneg hδ.le _))
    _ = ((4:ℝ)^κ*δ^κ*(F.card:ℝ))*(K^2*δ^κ) := by rw [hp]; ring
    _ ≤ (4:ℝ)^κ*δ^κ*(F.card:ℝ) := by
      exact (mul_le_mul_of_nonneg_left hbudget (by positivity)).trans_eq (mul_one _)
    _ ≤ (12:ℝ)^κ*r^κ*(F.card:ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul hbase hpow hδpow (by positivity)) (Nat.cast_nonneg _)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarNormalizedCoefficients
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalize a weak coefficient Frostman bound to a fixed constant in
 [1/3,1], including every radius down to the original fine resolution. -/
namespace Falconer

 theorem scalar_normalized_coefficients_candidate {δ κ K : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hκ : 0 ≤ κ) (hK : 1 ≤ K) (hbudget : K^2*δ^κ ≤ 1)
    (E : Finset ℝ) (hE : E.Nonempty) (hbound : ∀ x ∈ E, |x| ≤ 1)
    (hball : ∀ u r : ℝ, δ ≤ r → r ≤ 1 →
      scalarBallMass E u r ≤ K*r^(2*κ)*(E.card:ℝ)) :
    ∃ z ∈ E, ∃ R : ℝ, δ ≤ R ∧ R ≤ 2 ∧ (z,R) ∈ scalarBallCandidates δ E ∧
      1 ≤ (2:ℝ)^κ*K*R^κ ∧
      let F := E.filter fun x => |x-z| ≤ R
      let A := scalarZoom (z-3*R) (6*R) F
      A.Nonempty ∧ (∀ t ∈ A, 1/3 ≤ t ∧ t ≤ 1) ∧
      (E.card:ℝ) ≤ (4:ℝ)^κ*K*(A.card:ℝ) ∧
      ∀ u r : ℝ, δ ≤ r → r ≤ 1 →
        scalarBallMass A u r ≤ (12:ℝ)^κ*r^κ*(A.card:ℝ) := by
  classical
  obtain ⟨z,hz,R,hRδ,hR2,hcandidate,hF,hmax,hlocal⟩ :=
    scalar_maximal_density_interval_candidate hδ hδ1 hκ E hE hbound
  have hR : 0 < R := hδ.trans_le hRδ
  have hN : (0:ℝ) < (E.card:ℝ) := by exact_mod_cast hE.card_pos
  have hu : R ≤ 1 → scalarBallMass E z R ≤ K*R^(2*κ)*(E.card:ℝ) :=
    fun hR1 => hball z R hRδ hR1
  have hradius := scalar_density_radius_inequality hR hκ hK hN hmax hu
  have hrelative := scalar_density_relative_mass hR hκ hK hN hmax hu
  let F := E.filter fun x => |x-z| ≤ R
  let A := scalarZoom (z-3*R) (6*R) F
  have hFE : F ⊆ E := Finset.filter_subset _ _
  have hcard : A.card = F.card := scalarZoom_card (by positivity) F
  refine ⟨z,hz,R,hRδ,hR2,hcandidate,hradius,?_,?_,?_,?_⟩
  · exact hF.image _
  · exact scalar_positive_zoom_bounds hR F (fun x hx => (Finset.mem_filter.mp hx).2)
  · rw [hcard]
    exact hrelative
  · intro u r hr _
    by_cases hb : δ ≤ 6*R*r
    · exact scalar_positive_zoom_local_mass hδ hR E hlocal F hFE rfl u r hb
    · apply scalar_positive_zoom_small_mass hδ hκ (by linarith) hR E F hFE hrelative
        (fun u => hball u δ le_rfl hδ1) hbudget u r hr (le_of_not_ge hb)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarCoefficientExpressions
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact coefficient expressions used by the density normalization. -/
namespace Falconer
open scoped Pointwise

 theorem scalarCoefficientClosure_mono {i j : ℕ} (hij : i ≤ j) (S : Finset ℝ) :
    scalarCoefficientClosure S i ⊆ scalarCoefficientClosure S j := by
  induction hij with
  | refl => exact Finset.Subset.refl _
  | @step j _ ih => exact ih.trans (scalarCoefficientClosure_step S j)

 theorem scalar_coefficient_difference_mem (S : Finset ℝ) {x y : ℝ}
    (hx : x ∈ S) (hy : y ∈ S) : y-x ∈ scalarCoefficientClosure S 2 := by
  have hx1 : -x ∈ scalarCoefficientClosure S 1 := by
    exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.neg_mem_neg hx))
  have hy1 := scalarCoefficientClosure_step S 0 hy
  have hm := Finset.add_mem_add hy1 hx1
  exact Finset.mem_union_right _ (Finset.mem_union_left _ (by simpa [sub_eq_add_neg] using hm))

 theorem scalar_density_radius_mem {δ z R : ℝ} (E : Finset ℝ)
    (hcandidate : (z,R) ∈ scalarBallCandidates δ E) (hRδ : δ < R) :
    R ∈ scalarCoefficientClosure (E ∪ {1}) 3 := by
  let S := E ∪ {1}
  rcases Finset.mem_union.mp hcandidate with hp | hp
  · obtain ⟨⟨x,y⟩,hxy,he⟩ := Finset.mem_image.mp hp
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
    have heR : max δ |y-x| = R := congrArg Prod.snd he
    have hd : δ < |y-x| := by
      have hh : δ < max δ |y-x| := by rwa [heR]
      exact (lt_max_iff.mp hh).resolve_left (lt_irrefl _)
    have hdist : R = |y-x| := by simpa only [max_eq_right hd.le] using heR.symm
    rw [hdist]
    have hmem := scalar_coefficient_difference_mem S
      (Finset.mem_union_left _ hx) (Finset.mem_union_left _ hy)
    by_cases hnonneg : 0 ≤ y-x
    · rw [abs_of_nonneg hnonneg]
      exact scalarCoefficientClosure_step S 2 hmem
    · rw [abs_of_neg (lt_of_not_ge hnonneg)]
      exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.neg_mem_neg hmem))
  · obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hp
    have heR : (2:ℝ) = R := congrArg Prod.snd he
    rw [← heR]
    have h1 : (1:ℝ) ∈ S := Finset.mem_union_right _ (by simp)
    have h2 : (2:ℝ) ∈ scalarCoefficientClosure S 1 := by
      exact Finset.mem_union_right _ (Finset.mem_union_left _ (by
        rw [show (2:ℝ) = 1+1 by norm_num]
        exact Finset.add_mem_add h1 h1))
    exact scalarCoefficientClosure_mono (by omega) S h2

 theorem scalar_normalized_expression_mem {S : Finset ℝ} {a z R : ℝ}
    (ha : a ∈ S) (hz : z ∈ S) (hR : R⁻¹ ∈ S)
    (hhalf : (1/2:ℝ) ∈ S) (hsix : (1/6:ℝ) ∈ S) :
    (a-(z-3*R))/(6*R) ∈ scalarCoefficientClosure S 5 := by
  by_cases hR0 : R = 0
  · subst R
    simp only [mul_zero,div_zero]
    have hz0 : (0:ℝ) ∈ scalarCoefficientClosure S 2 := by
      simpa using scalar_coefficient_difference_mem S ha ha
    exact scalarCoefficientClosure_mono (by omega) S hz0
  have hd := scalar_coefficient_difference_mem S hz ha
  have hR2 := scalarCoefficientClosure_mono (show 0 ≤ 2 by omega) S hR
  have hm3 : (a-z)*R⁻¹ ∈ scalarCoefficientClosure S 3 :=
    Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mul_mem_mul hd hR2))
  have h63 := scalarCoefficientClosure_mono (show 0 ≤ 3 by omega) S hsix
  have hm4 : ((a-z)*R⁻¹)*(1/6:ℝ) ∈ scalarCoefficientClosure S 4 :=
    Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mul_mem_mul hm3 h63))
  have hh4 := scalarCoefficientClosure_mono (show 0 ≤ 4 by omega) S hhalf
  have hs5 : ((a-z)*R⁻¹)*(1/6:ℝ)+1/2 ∈ scalarCoefficientClosure S 5 :=
    Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.add_mem_add hm4 hh4))
  convert hs5 using 1
  all_goals try with_reducible_and_instances rfl
  field_simp
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarRationalProjection
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed rational coefficients have small projections under small
 doubling, by inclusion in an actual repeated sumset. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_reciprocal_integer_projection {δ K : ℝ} (hδ : 0 < δ)
    (X : Finset ℝ) (hX : X.Nonempty)
    (hdoubling : ((scalarCells δ (X+X)).card:ℝ) ≤ K*(scalarCells δ X).card)
    (m : ℕ) (hm : 0 < m) :
    ((scalarCells δ (X+X.image (fun x => (m:ℝ)⁻¹*x))).card:ℝ) ≤
      5*(m+3:ℝ)*(2*K)^(m+1)*(scalarCells δ X).card := by
  have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hsub : X+X.image (fun x => (m:ℝ)⁻¹*x) ⊆
      ((m+1) • X).image (fun x => (m:ℝ)⁻¹*x) := by
    intro z hz
    obtain ⟨x,hx,v,hv,rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
    have hxsum : (m:ℝ)*x ∈ m • X := by
      simpa only [nsmul_eq_mul] using (Finset.nsmul_mem_nsmul (n := m) hx)
    refine Finset.mem_image.mpr ⟨(m:ℝ)*x+y,?_,?_⟩
    · rw [succ_nsmul]
      exact Finset.add_mem_add hxsum hy
    · rw [mul_add,← mul_assoc,inv_mul_cancel₀ hmR.ne',one_mul]
  have hsmall : |(m:ℝ)⁻¹| ≤ (1:ℝ) := by
    rw [abs_of_pos (inv_pos.mpr hmR)]
    exact (inv_le_one₀ hmR).2 (by exact_mod_cast hm)
  have hd := scalar_dilation_cells (c := (m:ℝ)⁻¹) hδ ((m+1) • X) 1 (by simpa only [Nat.cast_one] using hsmall)
  have hp := scalar_pluennecke δ X X hX hdoubling (m+1) 0
  simp only [zero_nsmul,sub_zero,add_zero,Nat.cast_zero,Nat.cast_add,Nat.cast_one] at hp
  have hs : ((scalarCells δ (X+X.image (fun x => (m:ℝ)⁻¹*x))).card:ℝ) ≤
      5*((scalarCells δ ((m+1) • X)).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card (Finset.image_subset_image hsub)).trans hd
  calc
    _ ≤ 5*((scalarCells δ ((m+1) • X)).card:ℝ) := hs
    _ ≤ 5*((m+1+2:ℝ)*(2*K)^(m+1)*(scalarCells δ X).card) :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarNormalizedProjection
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small projections survive the precise coefficient density zoom.
 The budget is explicit and uses only a fixed number of scalar operations. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_normalized_projection_bound {δ K z R : ℝ} (hδ : 0 < δ) (hK : 1 ≤ K)
    (X E : Finset ℝ) (hX : X.Nonempty) (hz : z ∈ E)
    (hE : ∀ a ∈ E, |a| ≤ 1)
    (hcandidate : (z,R) ∈ scalarBallCandidates δ E) (hRδ : δ < R)
    (M : ℕ) (hM : |R⁻¹| ≤ M)
    (hdoubling : ((scalarCells δ (X+X)).card:ℝ) ≤ K*(scalarCells δ X).card)
    (hproj : ∀ a ∈ E, ((scalarCells δ (X+X.image (fun x => a*x))).card:ℝ) ≤
      K*(scalarCells δ X).card) :
    ∀ t ∈ scalarZoom (z-3*R) (6*R) (E.filter fun x => |x-z| ≤ R),
      ((scalarCells δ (X+X.image (fun x => t*x))).card:ℝ) ≤
        scalarNormalizedProjectionBudget M K*(scalarCells δ X).card := by
  have hK0 : 0 ≤ K := by linarith
  let S0 := E ∪ {1}
  have hS0 : ∀ a ∈ S0, |a| ≤ (1:ℝ) := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact hE a ha
    · have ha1 : a = 1 := Finset.mem_singleton.mp ha
      simp [ha1]
  have hproj0 : ∀ a ∈ S0, ((scalarCells δ (X+X.image (fun x => a*x))).card:ℝ) ≤
      K*(scalarCells δ X).card := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact hproj a ha
    · have he : a = 1 := Finset.mem_singleton.mp ha
      subst a
      simpa using hdoubling
  have hRmem := scalar_density_radius_mem E hcandidate hRδ
  have hRproj := scalar_closure_projections hδ hK X S0 hX 1 (by simpa only [Nat.cast_one] using hS0) hdoubling hproj0 3 R hRmem
  have hinv0 : ((scalarCells δ (X+X.image (fun x => R⁻¹*x))).card:ℝ) ≤
      (2*(M:ℝ)+3)*((scalarCells δ (X+X.image (fun x => R*x))).card:ℝ) := by
    exact_mod_cast scalar_inverse_coefficient_cells hδ (hδ.trans hRδ).ne' X M hM
  have hinv := hinv0.trans (mul_le_mul_of_nonneg_left hRproj (by positivity))
  have hhalf0 : ((scalarCells δ (X+X.image (fun x => (1/2:ℝ)*x))).card:ℝ) ≤
      25*(2*K)^3*(scalarCells δ X).card := by
    convert scalar_reciprocal_integer_projection hδ X hX hdoubling 2 (by omega) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
  have hhalf : ((scalarCells δ (X+X.image (fun x => (1/2:ℝ)*x))).card:ℝ) ≤
      45*(2*K)^7*(scalarCells δ X).card := by
    have hp := pow_le_pow_right₀ (show 1 ≤ 2*K by linarith) (show 3 ≤ (7:ℕ) by omega)
    apply hhalf0.trans
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    nlinarith [pow_nonneg (show 0 ≤ 2*K by positivity) 3]
  have hsix : ((scalarCells δ (X+X.image (fun x => (1/6:ℝ)*x))).card:ℝ) ≤
      45*(2*K)^7*(scalarCells δ X).card := by
    convert scalar_reciprocal_integer_projection hδ X hX hdoubling 6 (by omega) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
  let L := scalarNormalizedBaseBudget M K
  have hH : 0 ≤ scalarCoefficientBudget 1 K 3 :=
    (by norm_num : (0:ℝ) ≤ 1).trans (scalarCoefficientBudget_one_le 1 hK 3)
  have hrat0 : 0 ≤ 45*(2*K)^7 := by positivity
  have hinvnonneg : 0 ≤ (2*(M:ℝ)+3)*scalarCoefficientBudget 1 K 3 := by positivity
  have hL1 : 1 ≤ L := by dsimp [L,scalarNormalizedBaseBudget]; linarith
  have hLK : K ≤ L := by dsimp [L,scalarNormalizedBaseBudget]; linarith
  have hLrat : 45*(2*K)^7 ≤ L := by dsimp [L,scalarNormalizedBaseBudget]; linarith
  have hLinv : (2*(M:ℝ)+3)*scalarCoefficientBudget 1 K 3 ≤ L := by
    dsimp [L,scalarNormalizedBaseBudget]
    linarith
  let S := E ∪ {1,1/2,1/6,R⁻¹}
  have hS : ∀ a ∈ S, |a| ≤ (M+2:ℕ) := by
    intro a ha
    simp only [S,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with ha | rfl | rfl | rfl | rfl
    · exact (hE a ha).trans (by push_cast; linarith [(Nat.cast_nonneg M : (0:ℝ) ≤ (M:ℝ))])
    · push_cast; norm_num; linarith [(Nat.cast_nonneg M : (0:ℝ) ≤ (M:ℝ))]
    · push_cast; norm_num; linarith [(Nat.cast_nonneg M : (0:ℝ) ≤ (M:ℝ))]
    · push_cast; norm_num; linarith [(Nat.cast_nonneg M : (0:ℝ) ≤ (M:ℝ))]
    · exact hM.trans (by push_cast; linarith)
  have hprojS : ∀ a ∈ S, ((scalarCells δ (X+X.image (fun x => a*x))).card:ℝ) ≤
      L*(scalarCells δ X).card := by
    intro a ha
    simp only [S,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with ha | rfl | rfl | rfl | rfl
    · exact (hproj a ha).trans (mul_le_mul_of_nonneg_right hLK (Nat.cast_nonneg _))
    · have hh : ((scalarCells δ (X+X.image (fun x => (1:ℝ)*x))).card:ℝ) ≤
          K*(scalarCells δ X).card := by simpa using hdoubling
      exact hh.trans (mul_le_mul_of_nonneg_right hLK (Nat.cast_nonneg _))
    · exact hhalf.trans (mul_le_mul_of_nonneg_right hLrat (Nat.cast_nonneg _))
    · exact hsix.trans (mul_le_mul_of_nonneg_right hLrat (Nat.cast_nonneg _))
    · exact hinv.trans (by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right hLinv (Nat.cast_nonneg (scalarCells δ X).card))
  have hD := hdoubling.trans (mul_le_mul_of_nonneg_right hLK (Nat.cast_nonneg _))
  intro t ht
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp ht
  have hamem : a ∈ S := Finset.mem_union_left _ (Finset.mem_filter.mp ha).1
  have hzmem : z ∈ S := Finset.mem_union_left _ hz
  have hexpr := scalar_normalized_expression_mem (R := R) hamem hzmem
    (by simp [S]) (by simp [S]) (by simp [S])
  exact scalar_closure_projections hδ hL1 X S hX (M+2) hS hD hprojS 5 _ hexpr

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarCoefficientLogBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Logarithmic bounds for the fixed number of scalar coefficient operations.
 They keep the normalization cost polynomial in both numerical parameters. -/
namespace Falconer

 theorem scalar_coefficient_radius_bound (M n : ℕ) :
    (scalarCoefficientRadius M n:ℝ)+4 ≤ ((M:ℝ)+8)^(3^n) := by
  induction n with
  | zero => simp [scalarCoefficientRadius]; linarith
  | succ n ih =>
    let r : ℝ := scalarCoefficientRadius M n
    have hr : 0 ≤ r := Nat.cast_nonneg _
    have hpoly : 2*r^2+4 ≤ (r+4)^3 := by nlinarith [pow_nonneg hr 3]
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ r+4) ih 3
    calc
      _ = 2*r^2+4 := by simp only [scalarCoefficientRadius,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,r]
      _ ≤ (r+4)^3 := hpoly
      _ ≤ (((M:ℝ)+8)^(3^n))^3 := hh
      _ = _ := by rw [← pow_mul,pow_succ]

 theorem scalar_coefficient_radius_log (M n : ℕ) :
    Real.log ((scalarCoefficientRadius M n:ℝ)+4) ≤ (3:ℝ)^n*Real.log ((M:ℝ)+8) := by
  have hh := Real.log_le_log (by positivity : (0:ℝ) < (scalarCoefficientRadius M n:ℝ)+4)
    (scalar_coefficient_radius_bound M n)
  rw [Real.log_pow] at hh
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh

 theorem scalar_coefficient_log_budget (n : ℕ) :
    ∃ c p : ℝ, 0 ≤ c ∧ 0 ≤ p ∧ ∀ M : ℕ, ∀ K : ℝ, 1 ≤ K →
      Real.log (scalarCoefficientBudget M K n) ≤
        c+p*Real.log ((M:ℝ)+8)+(8:ℝ)^n*Real.log K := by
  induction n with
  | zero => exact ⟨0,0,le_rfl,le_rfl,fun M K _ => by simp [scalarCoefficientBudget]⟩
  | succ n ih =>
    obtain ⟨c,p,hc,hp,ih⟩ := ih
    refine ⟨Real.log 32768+8*c,(3:ℝ)^n+8*p,by positivity,by positivity,?_⟩
    intro M K hK
    have hKB : 0 < scalarCoefficientBudget M K n :=
      lt_of_lt_of_le (by norm_num) (scalarCoefficientBudget_one_le M hK n)
    have hr := scalar_coefficient_radius_log M n
    have hb := ih M K hK
    change Real.log (32768*((scalarCoefficientRadius M n:ℝ)+4)*
      (scalarCoefficientBudget M K n)^8) ≤ _
    rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by norm_num) (by positivity),
      Real.log_pow,pow_succ]
    norm_num only [Nat.cast_ofNat]
    nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarNormalizedLogBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalization cost grows at most polynomially with the weak
 Frostman constant and the original projection bound. -/
namespace Falconer

 theorem scalar_normalized_base_bound (M : ℕ) {K : ℝ} (hK : 1 ≤ K) :
    scalarNormalizedBaseBudget M K ≤ scalarNormalizedBaseConstant*((M:ℝ)+8)*K^512 := by
  have hH : 0 ≤ scalarCoefficientBudget 1 1 3 :=
    (by norm_num : (0:ℝ) ≤ 1).trans (scalarCoefficientBudget_one_le 1 (by norm_num) 3)
  have hK0 : 0 ≤ K := by linarith
  have hp1 : 1 ≤ K^512 := one_le_pow₀ hK
  have hp2 : K ≤ K^512 := by
    simpa only [pow_one] using pow_le_pow_right₀ hK (show 1 ≤ (512:ℕ) by omega)
  have hp7 : K^7 ≤ K^512 := pow_le_pow_right₀ hK (by omega)
  have hfactor : scalarCoefficientBudget 1 K 3 = scalarCoefficientBudget 1 1 3*K^512 := by
    simpa using scalarCoefficientBudget_factor 1 K 3
  have hh : scalarNormalizedBaseBudget M K ≤
      (5762+(2*(M:ℝ)+3)*scalarCoefficientBudget 1 1 3)*K^512 := by
    unfold scalarNormalizedBaseBudget
    rw [hfactor,mul_pow]
    norm_num only [show (2:ℝ)^7 = 128 by norm_num]
    nlinarith
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hK0 _)
  unfold scalarNormalizedBaseConstant
  nlinarith [(Nat.cast_nonneg M : (0:ℝ) ≤ (M:ℝ))]

 theorem scalar_normalized_base_one_le (M : ℕ) {K : ℝ} (hK : 1 ≤ K) :
    1 ≤ scalarNormalizedBaseBudget M K := by
  have hK0 : 0 ≤ K := by linarith
  have hH : 0 ≤ scalarCoefficientBudget 1 K 3 :=
    (by norm_num : (0:ℝ) ≤ 1).trans (scalarCoefficientBudget_one_le 1 hK 3)
  have hp : 0 ≤ 45*(2*K)^7 := by positivity
  have hm : 0 ≤ (2*(M:ℝ)+3)*scalarCoefficientBudget 1 K 3 := by positivity
  unfold scalarNormalizedBaseBudget
  linarith

 theorem scalar_normalized_log_budget :
    ∃ c p q : ℝ, 0 ≤ c ∧ 0 ≤ p ∧ 0 ≤ q ∧ ∀ M : ℕ, ∀ K : ℝ, 1 ≤ K →
      Real.log (scalarNormalizedProjectionBudget M K) ≤
        c+p*Real.log ((M:ℝ)+10)+q*Real.log K := by
  obtain ⟨c,p,hc,hp,hbudget⟩ := scalar_coefficient_log_budget 5
  have hC : 1 ≤ scalarNormalizedBaseConstant := by
    have hh := scalarCoefficientBudget_one_le 1 (K := (1:ℝ)) (by norm_num) 3
    unfold scalarNormalizedBaseConstant
    linarith
  have hClog : 0 ≤ Real.log scalarNormalizedBaseConstant := Real.log_nonneg hC
  refine ⟨c+32768*Real.log scalarNormalizedBaseConstant,p+32768,16777216,
    by positivity,by positivity,by norm_num,?_⟩
  intro M K hK
  have hb := hbudget (M+2) (scalarNormalizedBaseBudget M K)
    (scalar_normalized_base_one_le M hK)
  have hl := Real.log_le_log (lt_of_lt_of_le (by norm_num) (scalar_normalized_base_one_le M hK))
    (scalar_normalized_base_bound M hK)
  rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
    Real.log_pow] at hl
  have hm := Real.log_le_log (by positivity : (0:ℝ) < (M:ℝ)+8)
    (show (M:ℝ)+8 ≤ (M:ℝ)+10 by linarith)
  have hpm := mul_le_mul_of_nonneg_left hm (show (0:ℝ) ≤ 32768 by norm_num)
  change Real.log (scalarCoefficientBudget (M+2) (scalarNormalizedBaseBudget M K) 5) ≤ _
  push_cast at hb
  rw [show (M:ℝ)+2+8 = (M:ℝ)+10 by ring] at hb
  norm_num only [Nat.cast_ofNat,show (8:ℝ)^5 = 32768 by norm_num] at hb hl
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_ScalarDensityInverse
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalization radius has an inverse controlled by the original
 weak Frostman constant, with exactly the reserved exponent. -/
namespace Falconer

 theorem scalar_density_inverse_bound {R κ K : ℝ} (hR : 0 < R) (hκ : 0 < κ)
    (hK : 0 < K) (hbound : 1 ≤ (2:ℝ)^κ*K*R^κ) :
    R⁻¹ ≤ 2*K^(1/κ) := by
  have hpow : (R⁻¹)^κ ≤ (2:ℝ)^κ*K := by
    rw [Real.inv_rpow hR.le,inv_eq_one_div]
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hR κ)).2 (by nlinarith)
  have hh := Real.rpow_le_rpow (by positivity : 0 ≤ (R⁻¹)^κ) hpow
    (by positivity : 0 ≤ 1/κ)
  have hl : ((R⁻¹)^κ)^(1/κ) = R⁻¹ := by
    rw [← Real.rpow_mul (by positivity),mul_one_div_cancel hκ.ne',Real.rpow_one]
  have hr : ((2:ℝ)^κ*K)^(1/κ) = 2*K^(1/κ) := by
    rw [Real.mul_rpow (by positivity) hK.le,← Real.rpow_mul (by positivity),
      mul_one_div_cancel hκ.ne',Real.rpow_one]
  simpa only [hl,hr] using hh

 theorem scalar_density_radius_strict {δ κ K R : ℝ}
    (hδR : δ ≤ R) (hbound : 1 ≤ (2:ℝ)^κ*K*R^κ)
    (hsmall : (2:ℝ)^κ*K*δ^κ < 1) : δ < R := by
  apply lt_of_le_of_ne hδR
  intro he
  rw [he] at hsmall
  linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarNormalizationCost
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Eliminate the selected radius from the projection budget: its entire
 cost is controlled by logarithms of the original two weak constants. -/
namespace Falconer

 theorem scalar_normalization_radius_log {κ K : ℝ} (hκ : 0 < κ) (hK : 1 ≤ K) :
    Real.log ((scalarNormalizationRadius κ K:ℝ)+10) ≤
      Real.log 13+(1/κ)*Real.log K := by
  have hpow : 1 ≤ K^(1/κ) := Real.one_le_rpow hK (by positivity)
  have hc := (Nat.ceil_lt_add_one (by positivity : (0:ℝ) ≤ 2*K^(1/κ))).le
  have hbound : (scalarNormalizationRadius κ K:ℝ)+10 ≤ 13*K^(1/κ) := by
    change (⌈2*K^(1/κ)⌉₊:ℝ)+10 ≤ _
    linarith
  have hl := Real.log_le_log (by positivity : (0:ℝ) < (scalarNormalizationRadius κ K:ℝ)+10) hbound
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_rpow (by linarith : 0 < K)] at hl
  exact hl

 theorem scalar_normalization_cost {κ : ℝ} (hκ : 0 < κ) :
    ∃ c p q : ℝ, 0 ≤ c ∧ 0 ≤ p ∧ 0 ≤ q ∧ ∀ Kcoef Kproj : ℝ,
      1 ≤ Kcoef → 1 ≤ Kproj →
      Real.log (scalarNormalizedProjectionBudget (scalarNormalizationRadius κ Kcoef) Kproj) ≤
        c+p*Real.log Kcoef+q*Real.log Kproj := by
  obtain ⟨c,p,q,hc,hp,hq,hbound⟩ := scalar_normalized_log_budget
  refine ⟨c+p*Real.log 13,p/κ,q,by positivity,by positivity,hq,?_⟩
  intro Kcoef Kproj hKcoef hKproj
  have hh := hbound (scalarNormalizationRadius κ Kcoef) Kproj hKproj
  have hr := mul_le_mul_of_nonneg_left (scalar_normalization_radius_log hκ hKcoef) hp
  calc
    _ ≤ c+p*(Real.log 13+(1/κ)*Real.log Kcoef)+q*Real.log Kproj := by linarith
    _ = _ := by ring

 theorem scalar_density_inverse_radius {κ K R : ℝ} (hκ : 0 < κ) (hK : 0 < K)
    (hR : 0 < R) (hbound : 1 ≤ (2:ℝ)^κ*K*R^κ) :
    |R⁻¹| ≤ scalarNormalizationRadius κ K := by
  rw [abs_of_pos (inv_pos.mpr hR)]
  exact (scalar_density_inverse_bound hR hκ hK hbound).trans (Nat.le_ceil _)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarWeakScaleParameters
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One sufficiently small weak-loss exponent pays for all scalar
 normalization, fixed-fold sumset and prefix costs simultaneously. -/
namespace Falconer

 theorem scalar_weak_scale_parameters {κ η c p q : ℝ} (hκ : 0 < κ) (hη : 0 < η)
    (hc : 0 ≤ c) (hp : 0 ≤ p) (hq : 0 ≤ q) (B copies : ℕ) (hB : 0 < B) :
    ∃ ε : ℝ, ∃ M0 : ℕ, 0 < ε ∧ 0 < M0 ∧ ∀ M : ℕ, M0 ≤ M →
      let x := (B:ℝ)*(M:ℝ)*Real.log 2
      ε*x ≤ κ^2*x/160 ∧
      Real.log (copies+2:ℝ)+(copies:ℝ)*Real.log 2+(copies:ℝ)*ε*x ≤ κ*x/4 ∧
      (2*ε-κ)*x ≤ 0 ∧ κ*Real.log 2+(ε-κ)*x < 0 ∧
      c+(p+q)*ε*x ≤ η*(M:ℝ)*Real.log 2 := by
  have hBR : (0:ℝ) < (B:ℝ) := by exact_mod_cast hB
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let ε := min (κ^2/320) (min (κ/(8*((copies:ℝ)+1)))
    (min (κ/4) (η/(4*(B:ℝ)*(p+q+1)))))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have he1 : ε ≤ κ^2/320 := min_le_left _ _
  have he2 : ε ≤ κ/(8*((copies:ℝ)+1)) := (min_le_right _ _).trans (min_le_left _ _)
  have he3 : ε ≤ κ/4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have he4 : ε ≤ η/(4*(B:ℝ)*(p+q+1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hecopies : (copies:ℝ)*ε ≤ κ/8 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 8*((copies:ℝ)+1))).1 he2
    nlinarith
  have hecost : (p+q)*ε*(B:ℝ) ≤ η/4 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4*(B:ℝ)*(p+q+1))).1 he4
    have hn : 0 ≤ ε*(B:ℝ) := by positivity
    nlinarith
  let d := Real.log (copies+2:ℝ)+(copies:ℝ)*Real.log 2
  obtain ⟨M0,hM0⟩ := exists_nat_gt (max 3
    (max (2*c/(η*Real.log 2)) (8*d/(κ*(B:ℝ)*Real.log 2))))
  have hM03 : 3 ≤ M0 := by
    exact_mod_cast (le_of_lt ((le_max_left _ _).trans_lt hM0))
  have hc0 : 2*c ≤ η*(M0:ℝ)*Real.log 2 := by
    have hh := (div_lt_iff₀ (mul_pos hη hl)).1
      ((le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hM0))
    nlinarith
  have hd0 : 8*d ≤ κ*(B:ℝ)*(M0:ℝ)*Real.log 2 := by
    have hh := (div_lt_iff₀ (mul_pos (mul_pos hκ hBR) hl)).1
      ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hM0))
    nlinarith
  refine ⟨ε,M0,hε,by omega,?_⟩
  intro M hM
  dsimp only
  have hMR : (M0:ℝ) ≤ M := by exact_mod_cast hM
  have hM3 : (3:ℝ) ≤ M := by exact_mod_cast (hM03.trans hM)
  have hx : 0 ≤ (B:ℝ)*(M:ℝ)*Real.log 2 := by positivity
  have hcM : 2*c ≤ η*(M:ℝ)*Real.log 2 := by
    have hh := mul_le_mul_of_nonneg_left hMR (mul_nonneg hη.le hl.le)
    nlinarith
  have hdM : 8*d ≤ κ*(B:ℝ)*(M:ℝ)*Real.log 2 := by
    have hh := mul_le_mul_of_nonneg_left hMR (mul_nonneg (mul_nonneg hκ.le hBR.le) hl.le)
    nlinarith
  refine ⟨?_,?_,?_,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_right he1 hx
    nlinarith [sq_nonneg κ]
  · have hh := mul_le_mul_of_nonneg_right hecopies hx
    dsimp [d] at hdM
    nlinarith
  · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hx
  · have hB1 : (1:ℝ) ≤ B := by exact_mod_cast hB
    have hBM : (3:ℝ) ≤ (B:ℝ)*(M:ℝ) := by nlinarith
    have hlo := mul_le_mul_of_nonneg_right hBM (mul_nonneg hκ.le hl.le)
    have hhi := mul_le_mul_of_nonneg_right he3 hx
    nlinarith
  · have hh := mul_le_mul_of_nonneg_right hecost
      (show 0 ≤ (M:ℝ)*Real.log 2 by positivity)
    nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarDyadicPowers
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact conversion between the dyadic scale and the exponential budgets
 used in the scalar projection proof. -/
namespace Falconer

 theorem scalar_dyadic_power (N : ℕ) (κ : ℝ) :
    ((1/2:ℝ)^N)^κ = Real.exp (-κ*(N:ℝ)*Real.log 2) := by
  have hh : Real.log (1/2:ℝ) = -Real.log 2 := by
    rw [show (1/2:ℝ) = (2:ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [Real.rpow_def_of_pos (by positivity),Real.log_pow,hh]
  congr 1
  ring

namespace Regularization

 theorem scalar_leaf_cells_card {N : ℕ} (L : Finset (CellPath 1))
    (hL : L ⊆ cubePaths 1 N) :
    (scalarCells ((1/2:ℝ)^N) (L.image scalarPathCenter)).card = L.card := by
  have hsep : ∀ x ∈ L.image scalarPathCenter, ∀ y ∈ L.image scalarPathCenter,
      x ≠ y → (1/2:ℝ)^N ≤ |x-y| := by
    intro x hx y hy hxy
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hy
    exact scalarPathCenter_separated ((mem_cubePaths 1 N p).mp (hL hp))
      ((mem_cubePaths 1 N q).mp (hL hq)) (fun h => hxy (congrArg scalarPathCenter h))
  exact (Finset.card_image_of_injOn (scalarCells_injective (by positivity) hsep)).trans
    (scalar_leaf_center_card L hL)

end Regularization
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarPointPaths
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Place actual scalar points in the existing half-open dyadic tree. -/
namespace Falconer.Regularization

 theorem scalarPointPath_mem (N : ℕ) {x : ℝ} (hx : 0 ≤ x ∧ x < 1) :
    scalarPointPath N x ∈ cubePaths 1 N := by
  simp only [scalarPointPath,dite_eq_left hx]
  exact (Classical.choose_spec (scalar_point_has_path N hx)).1

 theorem scalarPointPath_contains (N : ℕ) {x : ℝ} (hx : 0 ≤ x ∧ x < 1) :
    scalarUnitPoint x ∈ ((⟨0,1⟩ : DyadicCube 1).descendant (scalarPointPath N x)).carrier := by
  simp only [scalarPointPath,dite_eq_left hx]
  exact (Classical.choose_spec (scalar_point_has_path N hx)).2

 theorem scalar_point_path_error (N : ℕ) {x : ℝ} (hx : 0 ≤ x ∧ x < 1) :
    |x-scalarPathCenter (scalarPointPath N x)| ≤ (1/2:ℝ)^N/2 := by
  have hp := (mem_cubePaths 1 N _).mp (scalarPointPath_mem N hx)
  have hm := scalarPointPath_contains N hx 0
  have hs : ((⟨0,1⟩ : DyadicCube 1).descendant (scalarPointPath N x)).side = (1/2:ℝ)^N := by
    rw [DyadicCube.descendant_side,hp]
    simp only [div_pow,one_pow]
  change _ ≤ x ∧ x < _ at hm
  change |x-(_+_/2)| ≤ _
  rw [hs]
  rw [hs] at hm
  rw [abs_le]
  constructor <;> linarith

 theorem scalar_point_path_same {N : ℕ} {x y : ℝ} (hx : 0 ≤ x ∧ x < 1)
    (hy : 0 ≤ y ∧ y < 1) (heq : scalarPointPath N x = scalarPointPath N y) :
    |x-y| < (1/2:ℝ)^N := by
  have hp := (mem_cubePaths 1 N _).mp (scalarPointPath_mem N hx)
  have hm := scalarPointPath_contains N hx 0
  have hn := scalarPointPath_contains N hy 0
  rw [← heq] at hn
  have hs : ((⟨0,1⟩ : DyadicCube 1).descendant (scalarPointPath N x)).side = (1/2:ℝ)^N := by
    rw [DyadicCube.descendant_side,hp]
    simp only [div_pow,one_pow]
  change _ ≤ x ∧ x < _ at hm
  change _ ≤ y ∧ y < _ at hn
  rw [hs] at hm hn
  rw [abs_lt]
  constructor <;> linarith

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarRounding
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rounding an actual separated scalar set to dyadic centers preserves
 its cardinality and moves each point by at most half a fine cell. -/
namespace Falconer.Regularization

 theorem scalarPointLeaves_subset (N : ℕ) (X : Finset ℝ)
    (hX : ∀ x ∈ X, 0 ≤ x ∧ x < 1) : scalarPointLeaves N X ⊆ cubePaths 1 N := by
  intro p hp
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
  exact scalarPointPath_mem N (hX x hx)

 theorem scalarPointLeaves_card (N : ℕ) (X : Finset ℝ)
    (hX : ∀ x ∈ X, 0 ≤ x ∧ x < 1)
    (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → (1/2:ℝ)^N ≤ |x-y|) :
    (scalarPointLeaves N X).card = X.card := by
  apply Finset.card_image_of_injOn
  intro x hx y hy heq
  by_contra hne
  exact (not_lt_of_ge (hsep x hx y hy hne)) (scalar_point_path_same (hX x hx) (hX y hy) heq)

 theorem scalarRoundedPoints_eq_image (N : ℕ) (X : Finset ℝ) :
    scalarRoundedPoints N X = X.image (fun x => scalarPathCenter (scalarPointPath N x)) := by
  simp only [scalarRoundedPoints,scalarPointLeaves,Finset.image_image,Function.comp_def]

 theorem scalarRoundedPoints_card (N : ℕ) (X : Finset ℝ)
    (hX : ∀ x ∈ X, 0 ≤ x ∧ x < 1)
    (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → (1/2:ℝ)^N ≤ |x-y|) :
    (scalarRoundedPoints N X).card = X.card := by
  exact (scalar_leaf_center_card _ (scalarPointLeaves_subset N X hX)).trans
    (scalarPointLeaves_card N X hX hsep)

 theorem scalarRoundedPoints_near (N : ℕ) (X : Finset ℝ)
    (hX : ∀ x ∈ X, 0 ≤ x ∧ x < 1) :
    ∀ y ∈ scalarRoundedPoints N X, ∃ x ∈ X, |y-x| ≤ (1/2:ℝ)^N/2 := by
  rw [scalarRoundedPoints_eq_image]
  intro y hy
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
  exact ⟨x,hx,by simpa only [abs_sub_comm] using scalar_point_path_error N (hX x hx)⟩

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarRoundingCovers
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar projection covers and ball counts are stable under the actual
 half-cell rounding used by the dyadic projection theorem. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_matched_projection_cover {δ a : ℝ} (hδ : 0 < δ) (ha : |a| ≤ 1)
    (X Y : Finset ℝ) (hnear : ∀ y ∈ Y, ∃ x ∈ X, |y-x| ≤ δ/2) :
    (scalarCells δ (Y+Y.image (fun x => a*x))).card ≤
      5*(scalarCells δ (X+X.image (fun x => a*x))).card := by
  apply scalarCells_near_card_nat hδ _ _ 1
  intro z hz
  obtain ⟨y,hy,v,hv,rfl⟩ := Finset.mem_add.mp hz
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨x,hx,hyx⟩ := hnear y hy
  obtain ⟨u,hu,hwu⟩ := hnear w hw
  refine ⟨x+a*u,Finset.add_mem_add hx (Finset.mem_image.mpr ⟨u,hu,rfl⟩),?_⟩
  have hm := mul_le_mul ha hwu (abs_nonneg (w-u)) (by norm_num : (0:ℝ) ≤ 1)
  calc
    |y+a*w-(x+a*u)| = |(y-x)+a*(w-u)| := by congr 1; ring
    _ ≤ |y-x|+|a*(w-u)| := abs_add_le _ _
    _ ≤ δ/2+δ/2 := by rw [abs_mul]; linarith
    _ = (1:ℕ)*δ := by norm_num

 theorem scalar_image_ball_bound {ρ : ℝ} (X : Finset ℝ) (f : ℝ → ℝ)
    (hnear : ∀ x ∈ X, |f x-x| ≤ ρ) (u r : ℝ) :
    scalarBallMass (X.image f) u r ≤ scalarBallMass X u (r+ρ) := by
  have hsub : (X.image f).filter (fun y => |y-u| ≤ r) ⊆
      (X.filter (fun x => |x-u| ≤ r+ρ)).image f := by
    intro y hy
    obtain ⟨hyX,hyB⟩ := Finset.mem_filter.mp hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hyX
    refine Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,?_⟩,rfl⟩
    have hh := abs_sub_le x (f x) u
    have he := hnear x hx
    rw [abs_sub_comm x (f x)] at hh
    linarith
  unfold scalarBallMass
  exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_image_le (s :=
    X.filter (fun x => |x-u| ≤ r+ρ)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarRoundingBalls
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original scalar Frostman estimate survives dyadic rounding with
 a fixed factor, including radii near the diameter of the unit interval. -/
namespace Falconer.Regularization

 theorem scalar_rounding_ball_bound (N : ℕ) (X : Finset ℝ)
    (hX : ∀ x ∈ X, 0 ≤ x ∧ x < 1)
    (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → (1/2:ℝ)^N ≤ |x-y|)
    {K κ : ℝ} (hK : 1 ≤ K) (hκ : 0 ≤ κ)
    (hball : ∀ u r : ℝ, (1/2:ℝ)^N ≤ r → r ≤ 1 →
      scalarBallMass X u r ≤ K*r^κ*(X.card:ℝ)) :
    ∀ u r : ℝ, (1/2:ℝ)^N ≤ r → r ≤ 1 →
      scalarBallMass (scalarRoundedPoints N X) u r ≤
        ((2:ℝ)^κ*K)*r^κ*((scalarRoundedPoints N X).card:ℝ) := by
  intro u r hr _
  have hδ : (0:ℝ) < (1/2:ℝ)^N := by positivity
  have hr0 : 0 < r := hδ.trans_le hr
  have hcard := scalarRoundedPoints_card N X hX hsep
  have hnear : ∀ x ∈ X, |scalarPathCenter (scalarPointPath N x)-x| ≤ (1/2:ℝ)^N/2 := by
    intro x hx
    simpa only [abs_sub_comm] using scalar_point_path_error N (hX x hx)
  have hm := scalar_image_ball_bound X (fun x => scalarPathCenter (scalarPointPath N x)) hnear u r
  rw [← scalarRoundedPoints_eq_image] at hm
  rw [hcard]
  by_cases hsmall : r ≤ 1/2
  · have hlow : (1/2:ℝ)^N ≤ r+(1/2:ℝ)^N/2 := by linarith
    have hhigh : r+(1/2:ℝ)^N/2 ≤ 1 := by linarith
    have hb := hball u (r+(1/2:ℝ)^N/2) hlow hhigh
    have hp := Real.rpow_le_rpow (by positivity : 0 ≤ r+(1/2:ℝ)^N/2)
      (show r+(1/2:ℝ)^N/2 ≤ 2*r by linarith) hκ
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hr0.le] at hp
    have hmul := mul_le_mul_of_nonneg_left hp (show 0 ≤ K*(X.card:ℝ) by positivity)
    nlinarith
  · have hp : 1 ≤ (2*r)^κ := Real.one_le_rpow (by linarith) hκ
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hr0.le] at hp
    have hmass : scalarBallMass (scalarRoundedPoints N X) u r ≤ (X.card:ℝ) := by
      unfold scalarBallMass
      rw [← hcard]
      exact_mod_cast Finset.card_filter_le _ _
    have hfactor : 1 ≤ (2:ℝ)^κ*K*r^κ := by nlinarith
    have hh := mul_le_mul_of_nonneg_right hfactor (Nat.cast_nonneg X.card)
    nlinarith

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarResolution
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Comparing scalar covering and ball counts at two nearby resolutions. -/
namespace Falconer

 theorem scalar_cells_resolution {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    (m : ℕ) (hscale : ρ ≤ (m:ℝ)*δ) (X : Finset ℝ) :
    (scalarCells δ X).card ≤ (2*m+3)*(scalarCells ρ X).card := by
  classical
  let q : ℝ → ℤ := fun x => ⌊x/ρ⌋
  let g := Function.invFunOn q (X : Set ℝ)
  let F := (scalarCells ρ X).image g
  have hnear : ∀ x ∈ X, ∃ y ∈ F, |x-y| ≤ (m:ℝ)*δ := by
    intro x hx
    have hrep := Function.invFunOn_pos (f := q) (s := (X : Set ℝ)) ⟨x,hx,rfl⟩
    have hd : |x-g (q x)| < ρ := same_scalar_cell_dist_lt hρ hrep.2.symm
    exact ⟨g (q x),Finset.mem_image.mpr ⟨q x,Finset.mem_image.mpr ⟨x,hx,rfl⟩,rfl⟩,
      hd.le.trans hscale⟩
  have hh := scalarCells_near_card_nat hδ X F m hnear
  have hc : (scalarCells δ F).card ≤ (scalarCells ρ X).card :=
    Finset.card_image_le.trans Finset.card_image_le
  exact hh.trans (Nat.mul_le_mul_left _ hc)

 theorem scalar_refined_ball_bound {δ ρ C K s : ℝ} (hδ : 0 < δ) (hρ1 : ρ ≤ 1)
    (hC : 1 ≤ C) (hscale : ρ ≤ C*δ) (hK : 0 ≤ K) (hs : 0 ≤ s) (X : Finset ℝ)
    (hball : ∀ u r : ℝ, ρ ≤ r → r ≤ 1 → scalarBallMass X u r ≤ K*r^s*(X.card:ℝ)) :
    ∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass X u r ≤
      (C^s*K)*r^s*(X.card:ℝ) := by
  intro u r hr hr1
  have hr0 : 0 < r := hδ.trans_le hr
  have hb := hball u (max r ρ) (le_max_right _ _) (max_le hr1 hρ1)
  have hm := scalarBallMass_radius_mono X u (le_max_left r ρ)
  have hmax : max r ρ ≤ C*r := by
    apply max_le
    · nlinarith
    · exact hscale.trans (mul_le_mul_of_nonneg_left hr (by linarith))
  have hp := Real.rpow_le_rpow (le_trans hr0.le (le_max_left _ _)) hmax hs
  rw [Real.mul_rpow (by linarith : 0 ≤ C) hr0.le] at hp
  have hh := mul_le_mul_of_nonneg_left hp (mul_nonneg hK (Nat.cast_nonneg X.card))
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarWeakProjection
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quantitative scalar projection theorem with weak Frostman constants.
 It is proved on the original dyadic point set, with no published input. -/
namespace Falconer.Regularization
open scoped Pointwise

 set_option maxHeartbeats 1000000 in
theorem scalar_weak_projection {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ B M0 : ℕ, ∃ ε : ℝ, 0 < B ∧ 0 < M0 ∧ 0 < ε ∧
      ∀ M : ℕ, M0 ≤ M →
      let δ := (1/2:ℝ)^(B*M)
      let W := Real.exp (ε*(B:ℝ)*(M:ℝ)*Real.log 2)
      ∀ L : Finset (CellPath 1), L ⊆ cubePaths 1 (B*M) → L.Nonempty →
      Real.log (L.card:ℝ) ≤ (1-κ)*(B:ℝ)*(M:ℝ)*Real.log 2 →
      ((scalarCells δ (L.image scalarPathCenter+L.image scalarPathCenter)).card:ℝ) ≤
        W*(L.card:ℝ) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass (L.image scalarPathCenter) u r ≤
        W*r^κ*(L.card:ℝ)) →
      ∀ E : Finset ℝ, E.Nonempty → (∀ a ∈ E, |a| ≤ 1) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass E u r ≤ W*r^(2*κ)*(E.card:ℝ)) →
      ∃ a ∈ E, W*(L.card:ℝ) <
        ((scalarCells δ (L.image scalarPathCenter+
          (L.image scalarPathCenter).image (fun x => a*x))).card:ℝ) := by
  obtain ⟨B,copies,η,hB,hcopies,hη,hgrowth⟩ :=
    scalar_weak_block_projection hκ hκ1 (by positivity : 0 < (12:ℝ)^κ)
  obtain ⟨c,p,q,hc,hp,hq,hcost⟩ := scalar_normalization_cost hκ
  obtain ⟨ε,M0,hε,hM0,hparameters⟩ := scalar_weak_scale_parameters hκ hη hc hp hq B copies hB
  refine ⟨B,M0,ε,hB,hM0,hε,?_⟩
  intro M hM
  dsimp only
  intro L hL hne hsize hadd hpoint E hE hEbound hEball
  let δ := (1/2:ℝ)^(B*M)
  let W := Real.exp (ε*(B:ℝ)*(M:ℝ)*Real.log 2)
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hW : 0 < W := Real.exp_pos _
  have hW1 : 1 ≤ W := Real.one_le_exp_iff.mpr (by positivity)
  obtain ⟨hprefix,hfold,hsmall,hstrict,hfinal⟩ := hparameters M hM
  have hballbudget : W^2*δ^κ ≤ 1 := by
    have he : W^2*δ^κ = Real.exp ((2*ε-κ)*(B:ℝ)*(M:ℝ)*Real.log 2) := by
      dsimp [W,δ]
      rw [pow_two,← Real.exp_add,scalar_dyadic_power,← Real.exp_add]
      push_cast
      congr 1
      ring
    rw [he]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  have hradiusbudget : (2:ℝ)^κ*W*δ^κ < 1 := by
    have he : (2:ℝ)^κ*W*δ^κ =
        Real.exp (κ*Real.log 2+(ε-κ)*(B:ℝ)*(M:ℝ)*Real.log 2) := by
      dsimp [W,δ]
      rw [Real.rpow_def_of_pos (by norm_num),scalar_dyadic_power,
        ← Real.exp_add,← Real.exp_add]
      push_cast
      congr 1
      ring
    rw [he]
    exact Real.exp_lt_one_iff.mpr (by nlinarith)
  obtain ⟨z,hz,R,hRδ,hR2,hcandidate,hradius,hA,hAb,hAsize,hAball⟩ :=
    scalar_normalized_coefficients_candidate hδ hδ1 hκ.le hW1 hballbudget E hE hEbound hEball
  let A := scalarZoom (z-3*R) (6*R) (E.filter fun x => |x-z| ≤ R)
  have hR : 0 < R := hδ.trans_le hRδ
  have hRstrict : δ < R := scalar_density_radius_strict hRδ hradius hradiusbudget
  have hcell : (scalarCells δ (L.image scalarPathCenter)).card = L.card := scalar_leaf_cells_card L hL
  have hLcard : (L.image scalarPathCenter).card = L.card := scalar_leaf_center_card L hL
  have hweak : Real.log W ≤ κ^2*(B:ℝ)*(M:ℝ)*Real.log 2/160 := by
    rw [show Real.log W = ε*(B:ℝ)*(M:ℝ)*Real.log 2 from Real.log_exp _]
    nlinarith
  have hsum : Real.log (copies+2:ℝ)+(copies:ℝ)*Real.log (2*W) ≤
      (κ/4)*(B:ℝ)*(M:ℝ)*Real.log 2 := by
    rw [Real.log_mul (by norm_num) hW.ne',show Real.log W =
      ε*(B:ℝ)*(M:ℝ)*Real.log 2 from Real.log_exp _]
    nlinarith
  have hadd' : ((scalarCells δ (L.image scalarPathCenter+L.image scalarPathCenter)).card:ℝ) ≤
      W*(scalarCells δ (L.image scalarPathCenter)).card := by rwa [hcell]
  have hpoint' : ∀ u r : ℝ, δ ≤ r → r ≤ 1 →
      scalarBallMass (L.image scalarPathCenter) u r ≤ W*r^κ*((L.image scalarPathCenter).card:ℝ) := by
    simpa only [hLcard] using hpoint
  obtain ⟨t,ht,hgain⟩ := hgrowth M (hM0.trans_le hM) W W hW hW hweak hsum L hL hne
    hsize hadd' hpoint' A hA hAb hAball
  by_contra hn
  push Not at hn
  have hproj : ∀ a ∈ E, ((scalarCells δ (L.image scalarPathCenter+
      (L.image scalarPathCenter).image (fun x => a*x))).card:ℝ) ≤
        W*(scalarCells δ (L.image scalarPathCenter)).card := by
    simpa only [hcell] using hn
  have hupper := scalar_normalized_projection_bound hδ hW1 (L.image scalarPathCenter) E
    (hne.image _) hz hEbound hcandidate hRstrict (scalarNormalizationRadius κ W)
    (scalar_density_inverse_radius hκ hW hR hradius) hadd' hproj t ht
  have hlog := hcost W W hW1 hW1
  rw [show Real.log W = ε*(B:ℝ)*(M:ℝ)*Real.log 2 from Real.log_exp _] at hlog
  have hlog' : Real.log (scalarNormalizedProjectionBudget (scalarNormalizationRadius κ W) W) ≤
      η*(M:ℝ)*Real.log 2 := by nlinarith
  have hpos : 0 < scalarNormalizedProjectionBudget (scalarNormalizationRadius κ W) W :=
    lt_of_lt_of_le (by norm_num) (scalarCoefficientBudget_one_le _
      (scalar_normalized_base_one_le _ hW1) _)
  have hb := Real.exp_le_exp.mpr hlog'
  rw [Real.exp_log hpos] at hb
  rw [hcell] at hupper
  have hh := hupper.trans (mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg L.card))
  exact (not_lt_of_ge hh) hgain

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarRoundingScale
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed losses of rounding fit into a quarter of the available
 scalar projection exponent at sufficiently fine scales. -/
namespace Falconer

 theorem scalar_rounding_scale {η κ : ℝ} (hη : 0 < η) (hκ : 0 ≤ κ)
    (B : ℕ) (hB : 0 < B) : ∃ M0 : ℕ, 0 < M0 ∧ ∀ M : ℕ, M0 ≤ M →
      5*Real.exp ((η/4)*(B:ℝ)*(M:ℝ)*Real.log 2) ≤ Real.exp (η*(B:ℝ)*(M:ℝ)*Real.log 2) ∧
      (2:ℝ)^κ*Real.exp ((η/4)*(B:ℝ)*(M:ℝ)*Real.log 2) ≤
        Real.exp (η*(B:ℝ)*(M:ℝ)*Real.log 2) := by
  have hb : (0:ℝ) < (B:ℝ) := by exact_mod_cast hB
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨M0,hM0⟩ := exists_nat_gt (max 1
    ((Real.log 5+κ*Real.log 2)/((3*η/4)*(B:ℝ)*Real.log 2)))
  have hM0pos : 0 < M0 := by
    have hh := (le_max_left _ _).trans_lt hM0
    exact_mod_cast (show (0:ℝ) < M0 by linarith)
  have hbase : Real.log 5+κ*Real.log 2 ≤ (3*η/4)*(B:ℝ)*(M0:ℝ)*Real.log 2 := by
    have hh := (div_lt_iff₀ (by positivity : 0 < (3*η/4)*(B:ℝ)*Real.log 2)).1
      ((le_max_right _ _).trans_lt hM0)
    nlinarith
  refine ⟨M0,hM0pos,?_⟩
  intro M hM
  have hh := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hM)
    (show 0 ≤ (3*η/4)*(B:ℝ)*Real.log 2 by positivity)
  have htotal : Real.log 5+κ*Real.log 2 ≤ (3*η/4)*(B:ℝ)*(M:ℝ)*Real.log 2 := by nlinarith
  have hlog5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  have hklog : 0 ≤ κ*Real.log 2 := mul_nonneg hκ hl.le
  constructor
  · calc
      _ = Real.exp (Real.log 5+(η/4)*(B:ℝ)*(M:ℝ)*Real.log 2) := by
        rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ) < 5)]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  · rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2),← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarScaleAlignment
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Align any fine dyadic resolution with a fixed block width. The
 difference is at most one block and all covering losses stay fixed. -/
namespace Falconer

 theorem scalar_block_ceiling_bounds (N B : ℕ) (hB : 0 < B) :
    N < B*(N/B+1) ∧ B*(N/B+1) ≤ N+B := by
  have hm := Nat.mod_lt N hB
  have he := Nat.mod_add_div N B
  rw [Nat.mul_add,Nat.mul_one]
  constructor <;> omega

 theorem scalar_block_scale_comparison (N B : ℕ) (hB : 0 < B) :
    (1/2:ℝ)^(B*(N/B+1)) ≤ (1/2:ℝ)^N ∧
    (1/2:ℝ)^N ≤ ((2:ℝ)^B)*(1/2:ℝ)^(B*(N/B+1)) := by
  obtain ⟨hlo,hhi⟩ := scalar_block_ceiling_bounds N B hB
  refine ⟨pow_le_pow_of_le_one (by norm_num) (by norm_num) hlo.le,?_⟩
  have hh := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ) ≤ 1) hhi
  rw [pow_add] at hh
  have hc : (2:ℝ)^B*(1/2:ℝ)^B = 1 := by rw [← mul_pow]; norm_num
  calc
    _ = ((2:ℝ)^B*(1/2:ℝ)^B)*(1/2:ℝ)^N := by rw [hc,one_mul]
    _ = (2:ℝ)^B*((1/2:ℝ)^N*(1/2:ℝ)^B) := by ring
    _ ≤ (2:ℝ)^B*(1/2:ℝ)^(B*(N/B+1)) := mul_le_mul_of_nonneg_left hh (by positivity)

 theorem scalar_fixed_losses {η C D : ℝ} (hη : 0 < η) (hC : 0 < C) (hD : 0 < D) :
    ∃ N0 : ℕ, 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      C*Real.exp ((η/4)*(N:ℝ)*Real.log 2) ≤ Real.exp (η*(N:ℝ)*Real.log 2) ∧
      D*Real.exp ((η/4)*(N:ℝ)*Real.log 2) ≤ Real.exp (η*(N:ℝ)*Real.log 2) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨N0,hN0⟩ := exists_nat_gt (max 1
    (max (Real.log C) (Real.log D)/((3*η/4)*Real.log 2)))
  have hNpos : 0 < N0 := by
    have hh := (le_max_left _ _).trans_lt hN0
    exact_mod_cast (show (0:ℝ) < N0 by linarith)
  have hbase : max (Real.log C) (Real.log D) ≤ (3*η/4)*(N0:ℝ)*Real.log 2 := by
    have hh := (div_lt_iff₀ (by positivity : 0 < (3*η/4)*Real.log 2)).1
      ((le_max_right _ _).trans_lt hN0)
    nlinarith
  refine ⟨N0,hNpos,?_⟩
  intro N hN
  have hh := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hN)
    (show 0 ≤ (3*η/4)*Real.log 2 by positivity)
  have hmax : max (Real.log C) (Real.log D) ≤ (3*η/4)*(N:ℝ)*Real.log 2 := by nlinarith
  constructor
  · calc
      _ = Real.exp (Real.log C+(η/4)*(N:ℝ)*Real.log 2) := by rw [Real.exp_add,Real.exp_log hC]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [le_max_left (Real.log C) (Real.log D)])
  · calc
      _ = Real.exp (Real.log D+(η/4)*(N:ℝ)*Real.log 2) := by rw [Real.exp_add,Real.exp_log hD]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [le_max_right (Real.log C) (Real.log D)])

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarUnitProjection
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar projection theorem for arbitrary separated points in the
 unit interval. Dyadic rounding has been removed from the hypotheses. -/
namespace Falconer.Regularization
open scoped Pointwise

 theorem scalar_unit_projection {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ B M0 : ℕ, ∃ ε : ℝ, 0 < B ∧ 0 < M0 ∧ 0 < ε ∧
      ∀ M : ℕ, M0 ≤ M →
      let δ := (1/2:ℝ)^(B*M)
      let W := Real.exp (ε*(B:ℝ)*(M:ℝ)*Real.log 2)
      ∀ X : Finset ℝ, X.Nonempty → (∀ x ∈ X, 0 ≤ x ∧ x < 1) →
      (∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|) →
      Real.log (X.card:ℝ) ≤ (1-κ)*(B:ℝ)*(M:ℝ)*Real.log 2 →
      ((scalarCells δ (X+X)).card:ℝ) ≤ W*(X.card:ℝ) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass X u r ≤ W*r^κ*(X.card:ℝ)) →
      ∀ E : Finset ℝ, E.Nonempty → (∀ a ∈ E, |a| ≤ 1) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass E u r ≤ W*r^(2*κ)*(E.card:ℝ)) →
      ∃ a ∈ E, W*(X.card:ℝ) < ((scalarCells δ (X+X.image (fun x => a*x))).card:ℝ) := by
  obtain ⟨B,N0,η,hB,hN0,hη,hgrowth⟩ := scalar_weak_projection hκ hκ1
  obtain ⟨N1,hN1,hscale⟩ := scalar_rounding_scale hη hκ.le B hB
  refine ⟨B,max N0 N1,η/4,hB,lt_of_lt_of_le hN0 (le_max_left _ _),by positivity,?_⟩
  intro M hM
  dsimp only
  intro X hX hXunit hsep hsize hadd hpoint E hE hEbound hEball
  let δ := (1/2:ℝ)^(B*M)
  let W := Real.exp ((η/4)*(B:ℝ)*(M:ℝ)*Real.log 2)
  let W0 := Real.exp (η*(B:ℝ)*(M:ℝ)*Real.log 2)
  have hδ : 0 < δ := by positivity
  have hW : 0 < W := Real.exp_pos _
  have hW1 : 1 ≤ W := Real.one_le_exp_iff.mpr (by positivity)
  obtain ⟨hfive,htwo⟩ := hscale M ((le_max_right _ _).trans hM)
  change 5*W ≤ W0 at hfive
  change (2:ℝ)^κ*W ≤ W0 at htwo
  have hWle : W ≤ W0 := by linarith
  let L := scalarPointLeaves (B*M) X
  have hL : L ⊆ cubePaths 1 (B*M) := scalarPointLeaves_subset _ X hXunit
  have hLne : L.Nonempty := hX.image _
  have hLcard : L.card = X.card := scalarPointLeaves_card _ X hXunit hsep
  have hYcard : (scalarRoundedPoints (B*M) X).card = X.card := scalarRoundedPoints_card _ X hXunit hsep
  have hnear := scalarRoundedPoints_near (B*M) X hXunit
  have hdoubling : ((scalarCells δ (L.image scalarPathCenter+L.image scalarPathCenter)).card:ℝ) ≤
      W0*(L.card:ℝ) := by
    have hh := scalar_matched_projection_cover (a := (1:ℝ)) hδ (by norm_num) X
      (scalarRoundedPoints (B*M) X) hnear
    have hh' : ((scalarCells δ (scalarRoundedPoints (B*M) X+scalarRoundedPoints (B*M) X)).card:ℝ) ≤
        5*((scalarCells δ (X+X)).card:ℝ) := by exact_mod_cast (by simpa using hh)
    change ((scalarCells δ (scalarRoundedPoints (B*M) X+scalarRoundedPoints (B*M) X)).card:ℝ) ≤ _
    rw [hLcard]
    have hm := mul_le_mul_of_nonneg_right hfive (Nat.cast_nonneg X.card)
    nlinarith
  have hballs : ∀ u r : ℝ, δ ≤ r → r ≤ 1 →
      scalarBallMass (L.image scalarPathCenter) u r ≤ W0*r^κ*(L.card:ℝ) := by
    intro u r hr hr1
    have hh := scalar_rounding_ball_bound (B*M) X hXunit hsep hW1 hκ.le hpoint u r hr hr1
    rw [hYcard] at hh
    have hm := mul_le_mul_of_nonneg_right htwo
      (mul_nonneg (Real.rpow_nonneg (hδ.le.trans hr) κ) (Nat.cast_nonneg X.card))
    change scalarBallMass (scalarRoundedPoints (B*M) X) u r ≤ _
    rw [hLcard]
    nlinarith
  have hEballs : ∀ u r : ℝ, δ ≤ r → r ≤ 1 →
      scalarBallMass E u r ≤ W0*r^(2*κ)*(E.card:ℝ) := by
    intro u r hr hr1
    have hh := hEball u r hr hr1
    have hm := mul_le_mul_of_nonneg_right hWle
      (mul_nonneg (Real.rpow_nonneg (hδ.le.trans hr) (2*κ)) (Nat.cast_nonneg E.card))
    nlinarith
  have hsizeL : Real.log (L.card:ℝ) ≤ (1-κ)*(B:ℝ)*(M:ℝ)*Real.log 2 := by rwa [hLcard]
  obtain ⟨a,ha,hgain⟩ := hgrowth M ((le_max_left _ _).trans hM) L hL hLne hsizeL
    hdoubling hballs E hE hEbound hEballs
  by_contra hn
  push Not at hn
  have hh := scalar_matched_projection_cover hδ (hEbound a ha) X
    (scalarRoundedPoints (B*M) X) hnear
  have hhR : ((scalarCells δ (scalarRoundedPoints (B*M) X+
      (scalarRoundedPoints (B*M) X).image (fun x => a*x))).card:ℝ) ≤
      5*((scalarCells δ (X+X.image (fun x => a*x))).card:ℝ) := by exact_mod_cast hh
  have hp := hn a ha
  have hm := mul_le_mul_of_nonneg_right hfive (Nat.cast_nonneg X.card)
  rw [hLcard] at hgain
  change W0*(X.card:ℝ) < ((scalarCells δ (scalarRoundedPoints (B*M) X+
    (scalarRoundedPoints (B*M) X).image (fun x => a*x))).card:ℝ) at hgain
  nlinarith

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarDyadicProjection
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar projection theorem at every sufficiently fine dyadic scale. -/
namespace Falconer.Regularization
open scoped Pointwise

 theorem scalar_dyadic_projection_oai {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let δ := (1/2:ℝ)^N
      let W := Real.exp (ε*(N:ℝ)*Real.log 2)
      ∀ X : Finset ℝ, X.Nonempty → (∀ x ∈ X, 0 ≤ x ∧ x < 1) →
      (∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|) →
      Real.log (X.card:ℝ) ≤ (1-κ)*(N:ℝ)*Real.log 2 →
      ((scalarCells δ (X+X)).card:ℝ) ≤ W*(X.card:ℝ) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass X u r ≤ W*r^κ*(X.card:ℝ)) →
      ∀ E : Finset ℝ, E.Nonempty → (∀ a ∈ E, |a| ≤ 1) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass E u r ≤ W*r^(2*κ)*(E.card:ℝ)) →
      ∃ a ∈ E, W*(X.card:ℝ) < ((scalarCells δ (X+X.image (fun x => a*x))).card:ℝ) := by
  obtain ⟨B,M0,η,hB,hM0,hη,hprojection⟩ := scalar_unit_projection hκ hκ1
  let C : ℝ := (2:ℝ)^B
  have hC : 1 ≤ C := one_le_pow₀ (by norm_num)
  let F : ℝ := (2*(2^B:ℕ)+3:ℕ)
  have hF : 0 < F := by positivity
  have hD : 0 < C^(2*κ) := by positivity
  obtain ⟨N1,hN1,hloss⟩ := scalar_fixed_losses hη hF hD
  refine ⟨η/4,max (B*M0) N1,by positivity,lt_of_lt_of_le hN1 (le_max_right _ _),?_⟩
  intro N hN
  dsimp only
  intro X hX hXunit hsep hsize hadd hpoint E hE hEbound hEball
  let M := N/B+1
  have hdepth : N < B*M := (scalar_block_ceiling_bounds N B hB).1
  have hNM : N ≤ B*M := hdepth.le
  have hNMreal : (N:ℝ) ≤ (B:ℝ)*(M:ℝ) := by exact_mod_cast hNM
  have hM : M0 ≤ M := by
    by_contra hn
    have hh := Nat.mul_le_mul_left B (show M ≤ M0 by omega)
    have hn0 : B*M0 ≤ N := (le_max_left _ _).trans hN
    omega
  let δ := (1/2:ℝ)^N
  let δf := (1/2:ℝ)^(B*M)
  let W := Real.exp ((η/4)*(N:ℝ)*Real.log 2)
  let Wf := Real.exp (η*(B:ℝ)*(M:ℝ)*Real.log 2)
  have hδ : 0 < δ := by positivity
  have hδf : 0 < δf := by positivity
  have hδ1 : δ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨hff,hcf⟩ := scalar_block_scale_comparison N B hB
  change δf ≤ δ at hff
  change δ ≤ C*δf at hcf
  have hW : 0 < W := Real.exp_pos _
  have hW1 : 1 ≤ W := Real.one_le_exp_iff.mpr (by positivity)
  have hExp : Real.exp (η*(N:ℝ)*Real.log 2) ≤ Wf := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hNMreal (show 0 ≤ η*Real.log 2 by positivity)
    nlinarith
  obtain ⟨hcover,hball⟩ := hloss N ((le_max_right _ _).trans hN)
  have hcover' : F*W ≤ Wf := hcover.trans hExp
  have hball' : C^(2*κ)*W ≤ Wf := hball.trans hExp
  have hCpow : C^κ ≤ C^(2*κ) := Real.rpow_le_rpow_of_exponent_le hC (by linarith)
  have hpointFactor : C^κ*W ≤ Wf :=
    (mul_le_mul_of_nonneg_right hCpow hW.le).trans hball'
  have hfineCover (Y : Finset ℝ) : ((scalarCells δf Y).card:ℝ) ≤ F*(scalarCells δ Y).card := by
    dsimp only [F]
    exact_mod_cast scalar_cells_resolution hδf hδ (2^B) (by
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using hcf) Y
  have hsizef : Real.log (X.card:ℝ) ≤ (1-κ)*(B:ℝ)*(M:ℝ)*Real.log 2 := by
    have hh := mul_le_mul_of_nonneg_left hNMreal
      (mul_nonneg (sub_nonneg.mpr hκ1) (Real.log_pos (by norm_num : (1:ℝ) < 2)).le)
    nlinarith
  have haddf : ((scalarCells δf (X+X)).card:ℝ) ≤ Wf*(X.card:ℝ) := by
    have hh := hfineCover (X+X)
    have hm := mul_le_mul_of_nonneg_left hadd hF.le
    have hf := mul_le_mul_of_nonneg_right hcover' (Nat.cast_nonneg X.card)
    nlinarith
  have hpointf : ∀ u r : ℝ, δf ≤ r → r ≤ 1 → scalarBallMass X u r ≤ Wf*r^κ*(X.card:ℝ) := by
    intro u r hr hr1
    have hh := scalar_refined_ball_bound hδf hδ1 hC hcf hW.le hκ.le X hpoint u r hr hr1
    have hm := mul_le_mul_of_nonneg_right hpointFactor
      (mul_nonneg (Real.rpow_nonneg (hδf.le.trans hr) κ) (Nat.cast_nonneg X.card))
    nlinarith
  have hcoefff : ∀ u r : ℝ, δf ≤ r → r ≤ 1 → scalarBallMass E u r ≤ Wf*r^(2*κ)*(E.card:ℝ) := by
    intro u r hr hr1
    have hh := scalar_refined_ball_bound hδf hδ1 hC hcf hW.le (by linarith : 0 ≤ 2*κ) E hEball u r hr hr1
    have hm := mul_le_mul_of_nonneg_right hball'
      (mul_nonneg (Real.rpow_nonneg (hδf.le.trans hr) (2*κ)) (Nat.cast_nonneg E.card))
    nlinarith
  obtain ⟨a,ha,hgain⟩ := hprojection M hM X hX hXunit
    (fun x hx y hy hxy => hff.trans (hsep x hx y hy hxy)) hsizef haddf hpointf E hE hEbound hcoefff
  by_contra hn
  push Not at hn
  have hh := hfineCover (X+X.image (fun x => a*x))
  have hp := mul_le_mul_of_nonneg_left (hn a ha) hF.le
  have hm := mul_le_mul_of_nonneg_right hcover' (Nat.cast_nonneg X.card)
  nlinarith

end Falconer.Regularization

end OAI
end

theorem solution : type_of% @OAI.Falconer.Regularization.scalar_dyadic_projection_oai := @OAI.Falconer.Regularization.scalar_dyadic_projection_oai

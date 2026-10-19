-- Prove2me | solution 1 for OAI.FiniteCircle.mask_character_branching
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:36:28.893706+00:00
-- url     : https://prove2.me/submissions/0b5d15a1-0eaf-4384-9fad-7bc7d32ad055

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/TreeBranching.lean:L266-L296
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.mask_character_branching. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Fourier
import Definitions.Def_OAI_Combinatorics_FiniteCircle_DyadicShifts
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TreeBranching
import Theorems.Thm_OAI_FiniteCircle_few_large_prime_divisors

-- ---- from OAI.Combinatorics.FiniteCircle.CircleWords ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

 theorem subcircle_injective {M p : ℕ} [NeZero M] [NeZero p] (hp : p ∣ M) :
    Function.Injective (subcircle hp) := by
  apply (injective_iff_map_eq_zero (subcircle hp)).mpr
  intro a ha
  rw [subcircle_val] at ha
  have hd := (ZMod.natCast_eq_zero_iff (M/p*a.val) M).mp ha
  have hM : M/p*p = M := Nat.div_mul_cancel hp
  have hpos : 0 < M/p := Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hp) (NeZero.pos p)
  have hd' : p ∣ a.val := by
    exact (Nat.mul_dvd_mul_iff_left hpos).mp (show M/p*p ∣ M/p*a.val by simpa only [hM] using hd)
  have haz := Nat.eq_zero_of_dvd_of_lt hd' a.val_lt
  exact (ZMod.val_eq_zero a).mp haz

namespace PhaseCost
variable {G : Type*} [AddCommGroup G]

end PhaseCost

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.DyadicShifts ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

 theorem zmod_character_mul {M : ℕ} [NeZero M] (x y : ZMod M) :
    AddChar.zmodAddEquiv x y = AddChar.zmodAddEquiv (x*y) 1 := by
  change ((AddChar.zmod M x y : Circle) : ℂ) = ((AddChar.zmod M (x*y) 1 : Circle) : ℂ)
  simp only [AddChar.zmod, AddChar.compAddMonoidHom_apply, AddMonoidHom.comp_apply,
    AddMonoidHom.coe_mulLeft, mul_one]

 theorem zmod_character_one_injective {M : ℕ} [NeZero M] :
    Function.Injective (fun x : ZMod M => AddChar.zmodAddEquiv x 1) := by
  intro x y h
  dsimp only at h
  apply AddChar.zmodAddEquiv.injective
  apply AddChar.ext
  intro a
  obtain ⟨b,rfl⟩ := ZMod.natCast_zmod_surjective a
  have hx (z : ZMod M) : AddChar.zmodAddEquiv z (b : ZMod M) =
      (AddChar.zmodAddEquiv z 1)^b := by
    rw [← nsmul_one (n := b), AddChar.map_nsmul_eq_pow]
  rw [hx, hx, h]

 theorem zmod_character_eq_one {M : ℕ} [NeZero M] (x y : ZMod M) :
    AddChar.zmodAddEquiv x y = 1 ↔ x*y = 0 := by
  rw [zmod_character_mul]
  have hz : AddChar.zmodAddEquiv (0 : ZMod M) 1 = 1 := by
    rw [map_zero]; rfl
  rw [← hz]
  exact zmod_character_one_injective.eq_iff

 theorem character_single {I : Type*} [DecidableEq I] {M : ℕ} [NeZero M]
    (χ : AddChar (I → ZMod M) ℂ) (i : I) (a : ZMod M) :
    χ (Pi.single i a) = AddChar.zmodAddEquiv (coordinateFrequency χ i) a := by
  rw [coordinateFrequency, AddEquiv.apply_symm_apply]
  rfl

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.MaskBranching ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem many_mask_children {h : ℕ} (hh : 2 ≤ h) (p : Fin h → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (hlarge : ∀ i, h ^ 3 ≤ p i) (f : (Σ k : Fin h, Fin (p k)) → ℤ)
    {β : ℤ} (hβ : β ≠ 0) (hsmall : β.natAbs < h ^ h)
    (hc : ∀ k, (p k : ℤ) ∣ β + ∑ b : Fin (p k), (b.val : ℤ) * f ⟨k, b⟩) :
    h ≤ 2 * (Finset.univ.filter fun j => f j ≠ 0).card := by
  classical
  let s := Finset.univ.filter fun j => f j ≠ 0
  let t := Finset.univ.filter fun k => ¬ (p k : ℤ) ∣ β
  let q := Finset.univ.filter fun k => (p k : ℤ) ∣ β
  have hq : 3 * q.card < h := few_large_prime_divisors hh p hp hinj hlarge hβ hsmall
  have ht : t ⊆ s.image Sigma.fst := by
    intro k hk
    have hk' : ¬ (p k : ℤ) ∣ β := (Finset.mem_filter.mp hk).2
    have hex : ∃ b : Fin (p k), f ⟨k, b⟩ ≠ 0 := by
      by_contra hn
      push Not at hn
      have hc' := hc k
      simp only [hn, mul_zero, Finset.sum_const_zero, add_zero] at hc'
      exact hk' hc'
    obtain ⟨b, hb⟩ := hex
    exact Finset.mem_image.mpr ⟨⟨k, b⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, rfl⟩
  have hcard : t.card ≤ s.card :=
    (Finset.card_le_card ht).trans (Finset.card_image_le)
  have hcount : q.card + t.card = h := by
    simpa [q, t] using (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin h))) (fun k => (p k : ℤ) ∣ β))
  change h ≤ 2 * s.card
  omega

theorem frequencySum_natAbs_le_mass (J : ℕ → Type) [∀ l, Fintype (J l)]
    (l : ℕ) (t : FrequencyTree J l) :
    (frequencySum J l t).natAbs ≤ frequencyMass J l t := by
  induction l with
  | zero => exact le_rfl
  | succ l ih =>
    exact (Int.natAbs_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ih (t j))

theorem mask_branching_induction {h : ℕ} (hh : 2 ≤ h) (p : ℕ → ℕ → ℕ)
    (hp : ∀ l (k : Fin h), 1 ≤ l → l ≤ h → Nat.Prime (p l k))
    (hinj : ∀ l, 1 ≤ l → l ≤ h → Function.Injective (fun k : Fin h => p l k))
    (hlarge : ∀ l (k : Fin h), 1 ≤ l → l ≤ h → h ^ 3 ≤ p l k)
    (l : ℕ) (hl : l ≤ h) (t : FrequencyTree (MaskChildren h p) l)
    (hc : MaskCongruences h p l t)
    (hroot : frequencySum (MaskChildren h p) l t ≠ 0)
    (hsmall : frequencyMass (MaskChildren h p) l t < h ^ h) :
    ((h : ℝ) / 2) ^ l ≤ (frequencyMass (MaskChildren h p) l t : ℝ) := by
  classical
  induction l with
  | zero =>
    have : 1 ≤ frequencyMass (MaskChildren h p) 0 t :=
      (Int.natAbs_pos.mpr hroot).trans_le (frequencySum_natAbs_le_mass _ _ _)
    simpa using (show (1 : ℝ) ≤ frequencyMass (MaskChildren h p) 0 t by exact_mod_cast this)
  | succ l ih =>
    let f : MaskChildren h p (l + 1) → ℤ := fun j => frequencySum (MaskChildren h p) l (t j)
    let s := Finset.univ.filter fun j => f j ≠ 0
    have hsumSmall : (frequencySum (MaskChildren h p) (l + 1) t).natAbs < h ^ h :=
      (frequencySum_natAbs_le_mass _ _ _).trans_lt hsmall
    have hcard : h ≤ 2 * s.card :=
      many_mask_children hh (fun k => p (l + 1) k)
        (fun k => hp _ k (by omega) hl) (hinj _ (by omega) hl)
        (fun k => hlarge _ k (by omega) hl) f hroot hsumSmall hc.1
    have hchild : ∀ j, frequencyMass (MaskChildren h p) l (t j) < h ^ h := by
      intro j
      apply lt_of_le_of_lt _ hsmall
      change frequencyMass (MaskChildren h p) l (t j) ≤ ∑ j, frequencyMass (MaskChildren h p) l (t j)
      exact Finset.single_le_sum (f := fun j => frequencyMass (MaskChildren h p) l (t j))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have hm : ∀ j ∈ s, ((h : ℝ) / 2) ^ l ≤ frequencyMass (MaskChildren h p) l (t j) := by
      intro j hj
      exact ih (by omega) (t j) (hc.2 j) (Finset.mem_filter.mp hj).2 (hchild j)
    have hcardR : (h : ℝ) / 2 ≤ s.card := by
      have : (h : ℝ) ≤ 2 * (s.card : ℝ) := by exact_mod_cast hcard
      linarith
    calc
      ((h : ℝ) / 2) ^ (l + 1) = ((h : ℝ) / 2) * ((h : ℝ) / 2) ^ l := by ring
      _ ≤ s.card * ((h : ℝ) / 2) ^ l := mul_le_mul_of_nonneg_right hcardR (by positivity)
      _ = ∑ j ∈ s, ((h : ℝ) / 2) ^ l := by simp
      _ ≤ ∑ j ∈ s, (frequencyMass (MaskChildren h p) l (t j) : ℝ) := Finset.sum_le_sum hm
      _ ≤ ∑ j, (frequencyMass (MaskChildren h p) l (t j) : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
      _ = (frequencyMass (MaskChildren h p) (l + 1) t : ℝ) := by
        simp only [frequencyMass, Nat.cast_sum]

theorem mask_frequency_branching {h : ℕ} (hh : 2 ≤ h) (p : ℕ → ℕ → ℕ)
    (hp : ∀ l (k : Fin h), 1 ≤ l → l ≤ h → Nat.Prime (p l k))
    (hinj : ∀ l, 1 ≤ l → l ≤ h → Function.Injective (fun k : Fin h => p l k))
    (hlarge : ∀ l (k : Fin h), 1 ≤ l → l ≤ h → h ^ 3 ≤ p l k)
    (t : FrequencyTree (MaskChildren h p) h) (hc : MaskCongruences h p h t)
    (hroot : frequencySum (MaskChildren h p) h t ≠ 0) :
    ((h : ℝ) / 2) ^ h ≤ (frequencyMass (MaskChildren h p) h t : ℝ) := by
  by_contra hn
  have hlt := lt_of_not_ge hn
  have hcap : ((h : ℝ) / 2) ^ h ≤ (h : ℝ) ^ h := by
    apply pow_le_pow_left₀ (by positivity)
    have : (0 : ℝ) ≤ h := Nat.cast_nonneg h
    linarith
  have hsmall : frequencyMass (MaskChildren h p) h t < h ^ h := by
    exact_mod_cast hlt.trans_le hcap
  exact (not_lt_of_ge (mask_branching_induction hh p hp hinj hlarge h le_rfl t hc hroot hsmall)) hlt

-- [generator] dropped (set where defined): attribute [reducible] MaskChildren

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.TreeBranching ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

 theorem treeCheap_generator (J Z : ℕ → Type) [∀ l, AddCommGroup (Z l)] {M : ℕ}
    (σ : ∀ l, Z l →+ (J l → ZMod M)) (l : ℕ) (z : Z (l+1)) :
    (fun i : TreeLeaf J (l+1) => σ (l+1) z i.1) ∈ treeCheap J Z σ (l+1) := by
  exact ⟨0, fun _ => (treeCheap J Z σ l).zero_mem, z, fun _ _ => (zero_add _).symm⟩

 theorem treeCheap_child (J Z : ℕ → Type) [∀ l, AddCommGroup (Z l)] {M : ℕ}
    (σ : ∀ l, Z l →+ (J l → ZMod M)) (l : ℕ) [DecidableEq (J (l+1))] (j : J (l+1))
    (c : TreeLeaf J l → ZMod M) (hc : c ∈ treeCheap J Z σ l) :
    (fun i : TreeLeaf J (l+1) => if i.1 = j then c i.2 else 0) ∈ treeCheap J Z σ (l+1) := by
  classical
  refine ⟨fun k => if k = j then c else 0, ?_, 0, ?_⟩
  · intro k
    dsimp only
    split_ifs
    · exact hc
    · exact (treeCheap J Z σ l).zero_mem
  · intro k i
    simp only [map_zero, Pi.zero_apply, add_zero]
    split_ifs <;> rfl

 theorem treeFrequency_sum (J : ℕ → Type) [∀ l, Fintype (J l)] (l : ℕ)
    (ξ : TreeLeaf J l → ℤ) : frequencySum J l (treeFrequency J l ξ) = ∑ i, ξ i := by
  induction l with
  | zero =>
    change ξ PUnit.unit = ∑ i : PUnit, ξ i
    exact (Fintype.sum_unique (fun i : PUnit => ξ i)).symm
  | succ l ih =>
    change (∑ j, frequencySum J l (treeFrequency J l (fun i => ξ (j,i)))) =
      ∑ i : J (l+1) × TreeLeaf J l, ξ i
    simp only [ih]
    exact (Fintype.sum_prod_type (fun i : J (l+1) × TreeLeaf J l => ξ i)).symm

 theorem treeFrequency_mass (J : ℕ → Type) [∀ l, Fintype (J l)] (l : ℕ)
    (ξ : TreeLeaf J l → ℤ) : frequencyMass J l (treeFrequency J l ξ) = ∑ i, (ξ i).natAbs := by
  induction l with
  | zero =>
    change (ξ PUnit.unit).natAbs = ∑ i : PUnit, (ξ i).natAbs
    exact (Fintype.sum_unique (fun i : PUnit => (ξ i).natAbs)).symm
  | succ l ih =>
    change (∑ j, frequencyMass J l (treeFrequency J l (fun i => ξ (j,i)))) =
      ∑ i : J (l+1) × TreeLeaf J l, (ξ i).natAbs
    simp only [ih]
    exact (Fintype.sum_prod_type (fun i : J (l+1) × TreeLeaf J l => (ξ i).natAbs)).symm

 theorem char_sum {G : Type*} [AddCommMonoid G] {I : Type*} (χ : AddChar G ℂ)
    (s : Finset I) (f : I → G) : χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, Finset.prod_insert hi,
      AddChar.map_add_eq_mul, ih]

 theorem character_dot {I : Type*} [Fintype I] [DecidableEq I] {M : ℕ} [NeZero M]
    (χ : AddChar (I → ZMod M) ℂ) (v : I → ZMod M) :
    χ v = AddChar.zmodAddEquiv (∑ i, coordinateFrequency χ i * v i) 1 := by
  classical
  have hv : v = ∑ i, Pi.single i (v i) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hv]
  rw [char_sum]
  rw [map_sum, AddChar.sum_apply]
  apply Finset.prod_congr rfl
  intro i _
  rw [character_single, zmod_character_mul]

 theorem character_dot_eq_one {I : Type*} [Fintype I] [DecidableEq I] {M : ℕ} [NeZero M]
    (χ : AddChar (I → ZMod M) ℂ) (v : I → ZMod M) :
    χ v = 1 ↔ ∑ i, coordinateFrequency χ i * v i = 0 := by
  rw [character_dot, zmod_character_eq_one, mul_one]

 theorem dot_restrict_child (J Z : ℕ → Type) [∀ l, Fintype (J l)]
    [∀ l, AddCommGroup (Z l)] {M : ℕ} (σ : ∀ l, Z l →+ (J l → ZMod M))
    (l : ℕ) (ξ : TreeLeaf J (l+1) → ℤ)
    (ha : ∀ c ∈ treeCheap J Z σ (l+1), ∑ i, (ξ i : ZMod M)*c i = 0)
    (j : J (l+1)) (c : TreeLeaf J l → ZMod M) (hc : c ∈ treeCheap J Z σ l) :
    ∑ i, (ξ (j,i):ZMod M)*c i = 0 := by
  classical
  have ht := ha _ (treeCheap_child J Z σ l j c hc)
  change (∑ k : J (l+1) × TreeLeaf J l, (ξ k : ZMod M)*(if k.1=j then c k.2 else 0)) = 0 at ht
  simpa only [Fintype.sum_prod_type, mul_ite, mul_zero, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using ht

 theorem mask_generator_apply {h M l : ℕ} {p : ℕ → ℕ → ℕ}
    (hd : ∀ k : Fin h, p l k ∣ M) (k : Fin h) (j : MaskTag h p l) :
    maskPhaseHom h p M l hd (Pi.single k 1) j =
      subcircle (hd k) 1 + if j.1 = k then j.2.val • subcircle (hd k) 1 else 0 := by
  classical
  have hs : (∑ a : Fin h, subcircle (hd a) ((Pi.single k 1 : MaskResidues h p l) a)) =
      subcircle (hd k) 1 := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro a _ ha
      simp [Pi.single_eq_of_ne ha]
    · simp
  change (∑ a : Fin h, subcircle (hd a) ((Pi.single k 1 : MaskResidues h p l) a)) +
    j.2.val • subcircle (hd j.1) ((Pi.single k 1 : MaskResidues h p l) j.1) = _
  rw [hs]
  congr 1
  by_cases he : j.1 = k
  · subst k
    simp
  · simp [he]

 theorem mask_dot_generator {h M l : ℕ} {p : ℕ → ℕ → ℕ}
    (hd : ∀ k : Fin h, p (l+1) k ∣ M) (k : Fin h)
    (ξ : TreeLeaf (MaskChildren h p) (l+1) → ℤ) :
    (∑ i, (ξ i:ZMod M)*maskPhaseHom h p M (l+1) hd (Pi.single k 1) i.1) =
      subcircle (hd k) (((∑ i, ξ i) + ∑ b : Fin (p (l+1) k), (b.val:ℤ)*
        ∑ i : TreeLeaf (MaskChildren h p) l, ξ (⟨k,b⟩,i) : ℤ) : ZMod (p (l+1) k)) := by
  classical
  rw [subcircle_intCast]
  let q : ZMod M := subcircle (hd k) 1
  have hq : q = (M/p (l+1) k : ZMod M) := by
    simpa only [Nat.cast_one, mul_one] using subcircle_natCast (hd k) 1
  simp_rw [mask_generator_apply]
  change (∑ i : MaskTag h p (l+1) × TreeLeaf (MaskChildren h p) l,
      (ξ i:ZMod M)*(q+if i.1.1=k then i.1.2.val • q else 0)) = _
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul]
  have hs : (∑ i : MaskTag h p (l+1) × TreeLeaf (MaskChildren h p) l,
      (ξ i:ZMod M)*(if i.1.1=k then i.1.2.val • q else 0)) =
      (∑ b : Fin (p (l+1) k), (b.val:ZMod M)*∑ i : TreeLeaf (MaskChildren h p) l,
        (ξ (⟨k,b⟩,i):ZMod M))*q := by
    rw [Fintype.sum_prod_type, Fintype.sum_sigma]
    simp only [mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero]
    rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ k)]
    simp_rw [nsmul_eq_mul, ← Finset.sum_mul]
    conv_rhs => rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hs, hq]
  push_cast
  ring

theorem mask_annihilator_congruences {h M : ℕ} {p : ℕ → ℕ → ℕ} [NeZero M]
    (hd : ∀ l (k : Fin h), p l k ∣ M) (hn : ∀ l (k : Fin h), 0 < p l k)
    (l : ℕ) (ξ : TreeLeaf (MaskChildren h p) l → ℤ)
    (ha : ∀ c ∈ maskCheap h p M hd l, ∑ i, (ξ i:ZMod M)*c i = 0) :
    MaskCongruences h p l (treeFrequency (MaskChildren h p) l ξ) := by
  classical
  induction l with
  | zero => trivial
  | succ l ih =>
    change (∀ k : Fin h, (p (l+1) k:ℤ) ∣ _ ) ∧ _
    constructor
    · intro k
      let : NeZero (p (l+1) k) := ⟨(hn _ k).ne'⟩
      have hg := treeCheap_generator (MaskChildren h p) (MaskResidues h p)
        (fun l => maskPhaseHom h p M l (hd _)) l (Pi.single k 1)
      have hz := ha _ hg
      rw [mask_dot_generator (hd (l+1)) k ξ] at hz
      have he : (((∑ i, ξ i) + ∑ b : Fin (p (l+1) k), (b.val:ℤ)*
          ∑ i : TreeLeaf (MaskChildren h p) l, ξ (⟨k,b⟩,i) : ℤ) : ZMod (p (l+1) k)) = 0 :=
        subcircle_injective (hd _ k) (hz.trans (map_zero _).symm)
      have he' := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp he
      simp only [treeFrequency, frequencySum, treeFrequency_sum]
      convert he' using 1
      congr 1
      exact (Fintype.sum_prod_type (fun i : MaskChildren h p (l+1) × TreeLeaf (MaskChildren h p) l => ξ i)).symm
    · intro j
      apply ih
      intro c hc
      exact dot_restrict_child (MaskChildren h p) (MaskResidues h p)
        (fun l => maskPhaseHom h p M l (hd _)) l ξ ha j c hc

theorem mask_character_branching {h M : ℕ} {p : ℕ → ℕ → ℕ} [NeZero M]
    (hh : 2 ≤ h) (hd : ∀ l (k : Fin h), p l k ∣ M)
    (hn : ∀ l (k : Fin h), 0 < p l k)
    (hp : ∀ l (k : Fin h), 1 ≤ l → l ≤ h → Nat.Prime (p l k))
    (hinj : ∀ l, 1 ≤ l → l ≤ h → Function.Injective (fun k : Fin h => p l k))
    (hlarge : ∀ l (k : Fin h), 1 ≤ l → l ≤ h → h ^ 3 ≤ p l k)
    (χ : AddChar (TreeLeaf (MaskChildren h p) h → ZMod M) ℂ)
    (ha : χ.compAddMonoidHom (maskCheap h p M hd h).subtype = 0)
    (θ : ZMod M) (hw : χ (fun _ => θ) ≠ 1) :
    ((h:ℝ)/2)^h ≤ ∑ i, ((coordinateFrequency χ i).valMinAbs.natAbs:ℝ) := by
  classical
  let ξ := fun i => (coordinateFrequency χ i).valMinAbs
  have hc := mask_annihilator_congruences hd hn h ξ (fun c hc => by
    have hv := congrArg (fun ψ : AddChar (maskCheap h p M hd h) ℂ => ψ ⟨c,hc⟩) ha
    have he : χ c = 1 := hv
    have hz := (character_dot_eq_one χ c).mp he
    simpa only [ξ, ZMod.coe_valMinAbs] using hz)
  have hroot : frequencySum (MaskChildren h p) h (treeFrequency (MaskChildren h p) h ξ) ≠ 0 := by
    rw [treeFrequency_sum]
    intro he
    apply hw
    rw [character_dot_eq_one, ← Finset.sum_mul]
    have hz : ∑ i, coordinateFrequency χ i = 0 := by
      have ht := congrArg (fun n : ℤ => (n : ZMod M)) he
      simpa only [Int.cast_sum, ξ, ZMod.coe_valMinAbs, Int.cast_zero] using ht
    rw [hz, zero_mul]
  have hb := mask_frequency_branching hh p hp hinj hlarge _ hc hroot
  rw [treeFrequency_mass] at hb
  simp only [Nat.cast_sum, ξ] at hb
  convert hb using 1
  all_goals congr 1

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module


theorem solution : type_of% @_root_.OAI.FiniteCircle.mask_character_branching := @_root_.OAI.FiniteCircle.mask_character_branching

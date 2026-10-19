-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Packing.integer_rows_eventual_pair_rank
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:04:39.27698+00:00
-- url     : https://prove2.me/submissions/a0256c8e-12a8-440c-b660-c751b6e5eb6f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/FiniteRank.lean:L268-L304
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Packing.integer_rows_eventual_pair_rank. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank

-- ---- from OAI.Analysis.Littlewood.FiniteRank ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uK uV uι uW uJ

namespace AsymptoticallyMinimalLittlewood
namespace Packing
noncomputable section
open scoped BigOperators
open Finset

section Linear
variable {K : Type uK} {V : Type uV} [Field K] [AddCommGroup V] [Module K V]

lemma functional_surjective {f : V →ₗ[K] K} (hf : f≠0) : Function.Surjective f := by
  obtain ⟨e,he⟩ : ∃ e, f e≠0 := by
    by_contra h; push Not at h; exact hf (LinearMap.ext h)
  intro a
  refine ⟨(a/f e) • e,?_⟩
  simp [he]

lemma nonparallel_pair_surjective {f g : V →ₗ[K] K} (hf : f≠0)
    (hfg : ∀ c : K, g≠c • f) : Function.Surjective (f.prod g) := by
  obtain ⟨e,he⟩ := functional_surjective hf (1 : K)
  have hk : ∃ y, f y=0 ∧ g y≠0 := by
    by_contra h
    push Not at h
    apply hfg (g e)
    ext x
    have hfx : f (x-f x • e)=0 := by simp [he]
    have hg := h _ hfx
    simp only [map_sub,map_smul,smul_eq_mul] at hg
    change g x=g e*f x
    exact (sub_eq_zero.mp hg).trans (mul_comm _ _)
  obtain ⟨y,hy,hgy⟩ := hk
  rintro ⟨a,b⟩
  refine ⟨a • e + ((b-a*g e)/g y) • y,?_⟩
  ext <;> simp [LinearMap.prod_apply,he,hy,hgy]

lemma pair_surjective_of_minor {ι : Type uι} [Fintype ι]
    (a b : ι → K) {i j : ι} (h : a i*b j-a j*b i≠0) :
    Function.Surjective ((dotForm a).prod (dotForm b)) := by
  classical
  have ha : dotForm a≠0 := by
    intro hz
    have hai : a i=0 := by
      simpa using congrArg (fun f : (ι → K) →ₗ[K] K ↦ f (Pi.single i 1)) hz
    have haj : a j=0 := by
      simpa using congrArg (fun f : (ι → K) →ₗ[K] K ↦ f (Pi.single j 1)) hz
    exact h (by simp [hai,haj])
  apply nonparallel_pair_surjective ha
  intro c hc
  have hbi : b i=c*a i := by
    simpa using congrArg (fun f : (ι → K) →ₗ[K] K ↦ f (Pi.single i 1)) hc
  have hbj : b j=c*a j := by
    simpa using congrArg (fun f : (ι → K) →ₗ[K] K ↦ f (Pi.single j 1)) hc
  apply h
  rw [hbi,hbj]
  ring

lemma exists_nonzero_minor {ι : Type uι} (a b : ι → K)
    (ha : a≠0) (hnp : ∀ c : K, b≠c • a) :
    ∃ i j, a i*b j-a j*b i≠0 := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, a i≠0 := by
    by_contra h; push Not at h; exact ha (funext h)
  by_contra h
  push Not at h
  apply hnp (b i/a i)
  ext j
  have he := h i j
  change b j=(b i/a i)*a j
  field_simp
  linear_combination he

end Linear

section Counting
variable {V : Type uV} {W : Type uW} [AddGroup V] [AddGroup W] [Fintype V] [Fintype W]
  [DecidableEq V] [DecidableEq W]

end Counting

section PairCounting
variable {K : Type uK} {V : Type uV} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]

end PairCounting
section PrimeRanks

lemma int_cast_ne_zero_of_large_prime {q : ℕ} [Fact q.Prime] {z : ℤ}
    (hz : z≠0) (hq : z.natAbs<q) : (z : ZMod q)≠0 := by
  intro h
  have hd : (q : ℤ) ∣ z := (ZMod.intCast_zmod_eq_zero_iff_dvd z q).mp h
  apply hz
  exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (by simpa using hq)

lemma pair_surjective_integer_minor {ι : Type uι} [Fintype ι]
    (a b : ι → ℤ) {i j : ι} (h : a i*b j-a j*b i≠0)
    {q : ℕ} [Fact q.Prime] (hq : (a i*b j-a j*b i).natAbs<q) :
    Function.Surjective ((dotForm (fun k ↦ (a k : ZMod q))).prod
      (dotForm (fun k ↦ (b k : ZMod q)))) := by
  apply pair_surjective_of_minor (i := i) (j := j)
  convert int_cast_ne_zero_of_large_prime h hq using 1 ; push_cast ; rfl

/-- The excluded-prime set is replaced by a concrete size threshold; this
suffices because only existence of one sufficiently large prime is needed. -/
lemma integer_rows_eventual_pair_rank {ι : Type uι} {J : Type uJ} [Fintype ι] [Fintype J]
    (a : J → ι → ℤ)
    (ha : ∀ j, (fun k ↦ (a j k : ℚ)) ≠ 0)
    (hnp : ∀ j l, j≠l → ∀ c : ℚ,
      (fun k ↦ (a l k : ℚ)) ≠ c • (fun k ↦ (a j k : ℚ))) :
    ∃ Q : ℕ, ∀ q : ℕ, ∀ (_hq : Fact q.Prime), Q<q →
      ∀ j l, j≠l → Function.Surjective
        ((dotForm (fun k ↦ (a j k : ZMod q))).prod
         (dotForm (fun k ↦ (a l k : ZMod q)))) := by
  classical
  let Q := ∑ j : J, ∑ l : J, ∑ k : ι, ∑ h : ι, (a j k*a l h-a j h*a l k).natAbs
  refine ⟨Q,?_⟩
  intro q hq hQ j l hjl
  obtain ⟨k,h,hm⟩ := exists_nonzero_minor (fun k ↦ (a j k : ℚ))
    (fun k ↦ (a l k : ℚ)) (ha j) (hnp j l hjl)
  have hi : a j k*a l h-a j h*a l k≠0 := by
    intro hz
    apply hm
    exact_mod_cast hz
  apply pair_surjective_integer_minor _ _ hi
  apply lt_of_le_of_lt _ hQ
  calc
    _ ≤ ∑ h : ι, (a j k*a l h-a j h*a l k).natAbs :=
      Finset.single_le_sum (f := fun h : ι ↦ (a j k*a l h-a j h*a l k).natAbs)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ h)
    _ ≤ ∑ k : ι, ∑ h : ι, (a j k*a l h-a j h*a l k).natAbs :=
      Finset.single_le_sum (f := fun k : ι ↦ ∑ h : ι, (a j k*a l h-a j h*a l k).natAbs)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ k)
    _ ≤ ∑ l : J, ∑ k : ι, ∑ h : ι, (a j k*a l h-a j h*a l k).natAbs :=
      Finset.single_le_sum (f := fun l : J ↦ ∑ k : ι, ∑ h : ι, (a j k*a l h-a j h*a l k).natAbs)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ l)
    _ ≤ Q := by
      dsimp [Q]
      exact Finset.single_le_sum (f := fun j : J ↦ ∑ l : J, ∑ k : ι, ∑ h : ι, (a j k*a l h-a j h*a l k).natAbs)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)

end PrimeRanks

end
end Packing
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Packing
open scoped BigOperators
open Finset


theorem solution.{uι,uJ} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.integer_rows_eventual_pair_rank.{uι,uJ} := @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.integer_rows_eventual_pair_rank.{uι,uJ}

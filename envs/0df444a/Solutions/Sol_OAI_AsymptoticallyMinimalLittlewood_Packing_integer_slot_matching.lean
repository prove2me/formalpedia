-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Packing.integer_slot_matching
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:35:59.903964+00:00
-- url     : https://prove2.me/submissions/dfd69433-c0da-4abd-8952-426efd3435b5

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/IntervalPacking.lean:L50-L136
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Packing.integer_slot_matching. The node keeps its source
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
import Definitions.Def_OAI_Analysis_Littlewood_Chunks
import Definitions.Def_OAI_Analysis_Littlewood_DependentMoments
import Definitions.Def_OAI_Analysis_Littlewood_SlotGraph
import Definitions.Def_OAI_Analysis_Littlewood_SlotParameters
import Definitions.Def_OAI_Analysis_Littlewood_IntervalPacking
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_concrete_slot_nv
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_concrete_slot_variance_le_av
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_integer_rows_eventual_pair_rank
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_packing_choose_R
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_packing_eventual_parameters
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_random_slot_matching

-- ---- from OAI.Analysis.Littlewood.Chunks ----
namespace OAI

universe uJ

namespace AsymptoticallyMinimalLittlewood
namespace Packing
noncomputable section
open scoped BigOperators
open Finset

variable {r : ℕ}
lemma prefix_add_length_le (L : Fin r → ℕ) (i : Fin r) :
    slotPrefix L i+L i ≤ periodLength L := by
  classical
  have hi : i∉Finset.Iio i := by simp
  dsimp [slotPrefix,periodLength]
  rw [add_comm,← Finset.sum_insert hi]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

lemma periodLength_pos (d : Fin r → ℕ) (i : Fin r) : 0<periodLength (oddLengths d) := by
  have h := prefix_add_length_le (oddLengths d) i
  dsimp [oddLengths] at h
  omega

end
end Packing
end AsymptoticallyMinimalLittlewood

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset
variable {r : ℕ}

attribute [local instance] Classical.propDecidable

end
end AsymptoticallyMinimalLittlewood.Packing

end OAI

-- ---- from OAI.Analysis.Littlewood.SlotParameters ----
namespace OAI

universe uV

/-! Parameter choices for the concrete signed-slot packing. The chunk
length is chosen first and remains fixed while the prime modulus grows. -/
namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open Filter Topology
open scoped BigOperators

lemma chunkCount_bounds {B q : ℕ} (hB : 0<B) (hq : 0<q) :
    B*chunkCount B q<q ∧ q≤B*(chunkCount B q+1) := by
  have hm := Nat.mod_lt (q-1) hB
  have he := Nat.mod_add_div (q-1) B
  dsimp [chunkCount]
  constructor
  · have hd := Nat.mul_div_le (q-1) B
    omega
  · nlinarith only [hm,he,show q-1+1=q by omega]

lemma chunkCount_pos {B q : ℕ} (hB : 0<B) (hq : B<q) : 0<chunkCount B q := by
  exact Nat.div_pos (by omega) hB

lemma packingBV_nonneg (r L R q : ℕ) (e p : ℝ) :
    0≤packingBV r L R e p q := by
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)) (sq_nonneg _)

end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset Nibble Filter Topology
attribute [local instance] Classical.propDecidable

end
end AsymptoticallyMinimalLittlewood.Packing

end OAI

-- ---- from OAI.Analysis.Littlewood.IntervalPacking ----
namespace OAI

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset Nibble Filter Topology
attribute [local instance] Classical.propDecidable

lemma scaled_slot_conditions {q v e p T n b r : ℝ} (hq : 0<q) (hp : 0<p)
    (hv : q^2≤v) (h1 : 1/q≤e*p) (h2 : T/q≤p) (h3 : T/q≤n-b)
    (h4 : b≤e*p/2) (h5 : n≤r) :
    T≤(v/q)*p ∧ T≤q*n-q*b ∧ v/q^2≤e*((v/q)*p) ∧
      (q*n)*(v/q^2)≤(r/p)*((v/q)*p) ∧
      (q*b)*(v/q^2)≤e*((v/q)*p)/2 := by
  let C := v/q^2
  have hC : 1≤C := (le_div_iff₀ (sq_pos_of_pos hq)).mpr (by simpa using hv)
  have hC0 : 0≤C := le_trans zero_le_one hC
  have hD : (v/q)*p=q*p*C := by dsimp [C]; field_simp
  have h1' : 1≤q*(e*p) := by simpa only [mul_comm] using (div_le_iff₀ hq).mp h1
  have h2' : T≤q*p := by simpa only [mul_comm] using (div_le_iff₀ hq).mp h2
  have h3' : T≤q*(n-b) := by simpa only [mul_comm] using (div_le_iff₀ hq).mp h3
  rw [hD]
  refine ⟨h2'.trans ?_,by nlinarith only [h3'],?_,?_,?_⟩
  · nlinarith only [hC,mul_pos hq hp]
  · change C≤e*(q*p*C)
    have h := mul_le_mul_of_nonneg_right h1' hC0
    nlinarith only [h]
  · change (q*n)*C≤(r/p)*(q*p*C)
    rw [show (r/p)*(q*p*C)=q*r*C by field_simp]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h5 hq.le) hC0
  · change (q*b)*C≤e*(q*p*C)/2
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 hq.le) hC0
    nlinarith only [h]

lemma choose_matching_loss {r L : ℕ} (hr : 0<r) (hL : 0<L) {t : ℝ}
    (ht0 : 0≤t) (ht : t<1/(2*L : ℝ)) :
    ∃ η : ℝ, 0<η ∧ η≤1 ∧ (r : ℝ)*t<(1-η)*((r : ℝ)/(2*L)) := by
  let η := (1-2*L*t)/2
  have hL' : (0 : ℝ)<2*L := by positivity
  have ht' := (lt_div_iff₀ hL').mp ht
  have hlt : t<(1-η)/(2*L) := by apply (lt_div_iff₀ hL').mpr; dsimp [η]; nlinarith
  have hr' : (0 : ℝ)<r := by exact_mod_cast hr
  refine ⟨η,by dsimp [η]; nlinarith,by dsimp [η]; nlinarith,?_⟩
  calc
    (r : ℝ)*t < r*((1-η)/(2*L)) := mul_lt_mul_of_pos_left hlt hr'
    _ = (1-η)*((r : ℝ)/(2*L)) := by ring

lemma integer_slot_matching {r m : ℕ} (hr : 2≤r)
    (a : Fin r → Fin m → ℤ)
    (ha : ∀ j, (fun k ↦ (a j k : ℚ))≠0)
    (hnp : ∀ j l, j≠l → ∀ c : ℚ,
      (fun k ↦ (a l k : ℚ))≠c • (fun k ↦ (a j k : ℚ)))
    (d : Fin r → ℕ) {t : ℝ} (ht0 : 0<t) (ht : t<1/(2*periodLength (oddLengths d) : ℝ)) :
    ∃ q R K : ℕ, q.Prime ∧ 3≤R ∧ 0<K ∧ 2*(K*(R*periodLength (oddLengths d)))<q ∧
      ∃ ω : SlotChoices d K, ∃ M : Finset (Fin m → ZMod q),
        (∀ y∈M, ∀ i, slotHit d R K q i ω (dotProduct (fun k ↦ (a i k : ZMod q)) y)) ∧
        (∀ y∈M, ∀ z∈M, y≠z → ∀ i,
          dotProduct (fun k ↦ (a i k : ZMod q)) y≠dotProduct (fun k ↦ (a i k : ZMod q)) z) ∧
        t*q<(M.card : ℝ) := by
  classical
  let i₀ : Fin r := ⟨0,by omega⟩
  let i₁ : Fin r := ⟨1,by omega⟩
  have hi : i₀≠i₁ := by intro h; have := congrArg Fin.val h; simp [i₀,i₁] at this
  have hr0 : 0<r := by omega
  let L := periodLength (oddLengths d)
  have hL : 0<L := periodLength_pos d i₀
  let p : ℝ := (1/(2*L : ℝ))^(r-1)
  have hp : 0<p := by dsimp [p]; positivity
  obtain ⟨η,hη,hη₁,hmargin⟩ := choose_matching_loss hr0 hL ht0.le ht
  obtain ⟨e,T,he,hT,hmatch⟩ := random_slot_matching (I := Fin r)
    (by simpa only [Fintype.card_fin] using (show 1≤r by omega)) (K₀ := (r : ℝ)/p) (by positivity) hη hη₁
  obtain ⟨R,hR,hBR,hSR,hNR,hMR⟩ := packing_choose_R hr0 hL he hp hmargin
  have hR0 : 0<R := by omega
  obtain ⟨Q,hQ⟩ := Filter.eventually_atTop.mp (packing_eventual_parameters hL hR0 he hp hBR hSR hNR hMR (T := T))
  obtain ⟨Q₀,hQ₀⟩ := integer_rows_eventual_pair_rank a ha hnp
  obtain ⟨q,hqq,hprime⟩ := Nat.exists_infinite_primes (max Q (max (Q₀+1) (2*R*L+1)))
  have hq0 : 0<q := hprime.pos
  have : Fact q.Prime := ⟨hprime⟩
  have hqpos : (0 : ℝ)<q := by exact_mod_cast hq0
  have hqq' : 2*R*L<q := by omega
  have hqpar := hQ q (by omega)
  let K := chunkCount (2*R*L) q
  have hK : 0<K := chunkCount_pos (by positivity) hqq'
  have hqslot : 2*(K*(R*L))<q := by
    have h := (chunkCount_bounds (show 0<2*R*L by positivity) hq0).1
    nlinarith only [h]
  let g : Fin r → (Fin m → ZMod q) →ₗ[ZMod q] ZMod q :=
    fun i ↦ dotForm (fun k ↦ (a i k : ZMod q))
  have hpair : ∀ i j, i≠j → Function.Surjective ((g i).prod (g j)) :=
    hQ₀ q inferInstance (by omega)
  have hg (i : Fin r) : Function.Surjective (g i) := by
    have hj : ∃ j : Fin r, i≠j := by
      by_cases h : i=i₀
      · exact ⟨i₁,h ▸ hi⟩
      · exact ⟨i₀,h⟩
    obtain ⟨j,hj⟩ := hj
    intro s
    obtain ⟨y,hy⟩ := hpair i j hj (s,0)
    exact ⟨y,congrArg Prod.fst hy⟩
  have hV : (q : ℝ)^2≤Fintype.card (Fin m → ZMod q) := by
    have h := Fintype.card_le_of_surjective _ (hpair i₀ i₁ hi)
    have h' : q*q≤Fintype.card (Fin m → ZMod q) := by
      simpa only [Fintype.card_prod,ZMod.card] using h
    rw [pow_two]
    exact_mod_cast h'
  have hc := scaled_slot_conditions hqpos hp hV hqpar.1 hqpar.2.1 hqpar.2.2.1
    hqpar.2.2.2.1 hqpar.2.2.2.2.1
  have : Nonempty (Fin L) := ⟨⟨0,hL⟩⟩
  obtain ⟨ω,M,hM,hdis,hsize⟩ := hmatch g (fun i s ω ↦ slotHit d R K q i ω s)
    p (max (packingAV r L R q) 0) ((q : ℝ)*packingBV r L R e p q) ((q : ℝ)*packingNV r L R q)
    hg hpair hp (mul_nonneg hqpos.le (packingBV_nonneg r L R q e p))
    (fun i ↦ (concrete_slot_variance_le_av d R i₀ (by omega) hqq' g hg hpair i).trans (le_max_left _ _))
    (by simp only [Fintype.card_fin,ZMod.card,packingBV]; ring_nf; exact le_rfl)
    (fun ω ↦ concrete_slot_nv d i₀ (by omega) ω)
    (by simpa only [ZMod.card] using hc.1)
    hc.2.1
    (by simpa only [ZMod.card] using hc.2.2.1)
    (by simpa only [ZMod.card] using hc.2.2.2.1)
    (by simpa only [ZMod.card] using hc.2.2.2.2)
  refine ⟨q,R,K,hprime,hR,hK,hqslot,ω,M,?_,?_,?_⟩
  · intro y hy i
    have hm := hM hy
    simp only [slotEdges,Finset.mem_filter,Finset.mem_univ,true_and] at hm
    exact hm i
  · intro y hy z hz hyz i hEq
    have hd := hdis hy hz hyz
    have hyv : (i,g i y)∈slotSupport g y := by simp [slotSupport]
    change g i y=g i z at hEq
    have hzv : (i,g i y)∈slotSupport g z := by rw [hEq]; simp [slotSupport]
    exact Finset.disjoint_left.mp hd hyv hzv
  · have hstrict := mul_lt_mul_of_pos_right hqpar.2.2.2.2.2 hqpos
    simp only [Fintype.card_fin] at hsize
    have hrpos : (0 : ℝ)<r := by exact_mod_cast hr0
    nlinarith only [hstrict,hsize,hrpos]

end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

end
end AsymptoticallyMinimalLittlewood.Packing

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Packing
open scoped BigOperators
open Finset Nibble Filter Topology
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.integer_slot_matching := @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.integer_slot_matching

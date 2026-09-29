-- Prove2me | solution 1 for LovaszSchrijver.IntegerHull.N_iter_card_eq_hull01
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T19:58:41.397717+00:00
-- url     : https://prove2.me/submissions/7c10392a-a0e0-4b7c-8cba-16c2f3c4e97b

import Mathlib
import Definitions.Def_LovaszSchrijver_IntegerHull_Basic
import Definitions.Def_LovaszSchrijver_IntegerHull_MatrixCone
open Matrix Pointwise

set_option autoImplicit false

namespace LS32d53bf7

open LovaszSchrijver.IntegerHull

variable {ι : Type}

/-! ### cone API -/

theorem subset_cone (S : Set (Option ι → ℝ)) : S ⊆ cone S := fun _ hx => by
  unfold cone
  exact Submodule.subset_span hx

theorem cone_induction {S : Set (Option ι → ℝ)} {P : (Option ι → ℝ) → Prop}
    (hS : ∀ x ∈ S, P x) (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hsmul : ∀ c : ℝ, 0 ≤ c → ∀ x, P x → P (c • x)) {x : Option ι → ℝ} (hx : x ∈ cone S) :
    P x := by
  unfold cone at hx
  have hx' : x ∈ PointedCone.hull ℝ S := hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy => exact hS y hy
  | zero => exact h0
  | add y z _ _ hy hz => exact hadd y z hy hz
  | smul a y _ hy => exact hsmul a a.2 y hy

theorem zero_mem_cone (S : Set (Option ι → ℝ)) : (0 : Option ι → ℝ) ∈ cone S := by
  unfold cone
  exact Submodule.zero_mem (PointedCone.hull ℝ S)

theorem add_mem_cone {S : Set (Option ι → ℝ)} {x y : Option ι → ℝ} (hx : x ∈ cone S)
    (hy : y ∈ cone S) : x + y ∈ cone S := by
  unfold cone at *
  exact Submodule.add_mem (PointedCone.hull ℝ S) hx hy

theorem smul_mem_cone {S : Set (Option ι → ℝ)} {c : ℝ} (hc : 0 ≤ c) {x : Option ι → ℝ}
    (hx : x ∈ cone S) : c • x ∈ cone S := by
  unfold cone at *
  exact Submodule.smul_mem (PointedCone.hull ℝ S) (⟨c, hc⟩ : {c : ℝ // 0 ≤ c}) hx

theorem cone_mono {S T : Set (Option ι → ℝ)} (h : S ⊆ T) {x : Option ι → ℝ}
    (hx : x ∈ cone S) : x ∈ cone T :=
  cone_induction (fun _ hy => subset_cone T (h hy)) (zero_mem_cone T)
    (fun _ _ => add_mem_cone) (fun _ hc _ => smul_mem_cone hc) hx

/-! ### bounds on Q -/

theorem Q_bounds {x : Option ι → ℝ} (hx : x ∈ (Q : Set (Option ι → ℝ))) :
    0 ≤ x none ∧ ∀ i, 0 ≤ x (some i) ∧ x (some i) ≤ x none := by
  have hx' : x ∈ cone {x : Option ι → ℝ | IsZeroOne x ∧ x none = 1} := hx
  refine cone_induction (P := fun x => 0 ≤ x none ∧ ∀ i, 0 ≤ x (some i) ∧ x (some i) ≤ x none)
    ?_ ?_ ?_ ?_ hx'
  · rintro p ⟨hp, hp0⟩
    refine ⟨by rw [hp0]; norm_num, fun i => ?_⟩
    rcases hp (some i) with h | h <;> rw [h, hp0] <;> norm_num
  · exact ⟨le_refl _, fun i => ⟨le_refl _, le_refl _⟩⟩
  · rintro x y ⟨hx0, hx⟩ ⟨hy0, hy⟩
    refine ⟨by simp only [Pi.add_apply]; linarith, fun i => ?_⟩
    have := hx i
    have := hy i
    simp only [Pi.add_apply]
    constructor <;> linarith [(hx i).1, (hx i).2, (hy i).1, (hy i).2]
  · rintro c hc x ⟨hx0, hx⟩
    refine ⟨by simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hc hx0, fun i => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    exact ⟨mul_nonneg hc (hx i).1, mul_le_mul_of_nonneg_left (hx i).2 hc⟩

/-! ### bipolar -/

theorem bipolar [Fintype ι] [DecidableEq ι] {C : Set (Option ι → ℝ)}
    (h0 : (0 : Option ι → ℝ) ∈ C)
    (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C) (hsmul : ∀ c : ℝ, 0 ≤ c → ∀ x ∈ C, c • x ∈ C)
    (hcl : IsClosed C) {z : Option ι → ℝ} (hz : ∀ u ∈ dualCone C, 0 ≤ u ⬝ᵥ z) : z ∈ C := by
  by_contra hzC
  have hconv : Convex ℝ C := by
    intro x hx y hy a b ha hb _
    exact hadd _ (hsmul a ha x hx) _ (hsmul b hb y hy)
  obtain ⟨f, u, hf, hfz⟩ := geometric_hahn_banach_closed_point hconv hcl hzC
  have hu : 0 < u := by
    have := hf 0 h0
    simpa using this
  have hle : ∀ a ∈ C, f a ≤ 0 := by
    intro a ha
    by_contra h
    have h : 0 < f a := not_le.1 h
    have hpos : 0 ≤ u / f a + 1 := by positivity
    have := hf ((u / f a + 1) • a) (hsmul _ hpos a ha)
    rw [map_smul, smul_eq_mul] at this
    have h2 : (u / f a + 1) * f a = u + f a := by field_simp
    linarith
  have hfw : ∀ x, f x = (fun j => f (fun k => if j = k then (1:ℝ) else 0)) ⬝ᵥ x := by
    intro x
    have := LinearMap.pi_apply_eq_sum_univ (f : (Option ι → ℝ) →ₗ[ℝ] ℝ) x
    simp only [ContinuousLinearMap.coe_coe] at this
    rw [this]
    simp only [dotProduct, smul_eq_mul]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  set w : Option ι → ℝ := fun j => f (fun k => if j = k then (1:ℝ) else 0) with hw
  have hmem : -w ∈ dualCone C := by
    intro a ha
    rw [neg_dotProduct, ← hfw]
    linarith [hle a ha]
  have := hz (-w) hmem
  rw [neg_dotProduct, ← hfw] at this
  linarith

/-! ### closedness of a sum of two bounded closed sets -/

theorem add_closed [Fintype ι] {A B : Set (Option ι → ℝ)} (hA : IsClosed A) (hB : IsClosed B)
    (hAb : ∀ a ∈ A, ‖a‖ ≤ a none) (hBb : ∀ b ∈ B, ‖b‖ ≤ b none) : IsClosed (A + B) := by
  refine isClosed_of_closure_subset (fun z hz => ?_)
  set R : ℝ := z none + 1 with hR
  have hU : IsOpen {y : Option ι → ℝ | y none < R} :=
    isOpen_lt (continuous_apply none) continuous_const
  have hzU : z ∈ {y : Option ι → ℝ | y none < R} := by
    show z none < R
    linarith
  have h1 : z ∈ closure ({y : Option ι → ℝ | y none < R} ∩ (A + B)) :=
    hU.inter_closure ⟨hzU, hz⟩
  have hP : IsCompact ((A ∩ Metric.closedBall 0 R) + (B ∩ Metric.closedBall 0 R)) :=
    ((isCompact_closedBall 0 R).inter_left hA).add ((isCompact_closedBall 0 R).inter_left hB)
  have hsub : {y : Option ι → ℝ | y none < R} ∩ (A + B) ⊆
      (A ∩ Metric.closedBall 0 R) + (B ∩ Metric.closedBall 0 R) := by
    rintro y ⟨hy, a, ha, b, hb, rfl⟩
    have h0a : 0 ≤ a none := (norm_nonneg a).trans (hAb a ha)
    have h0b : 0 ≤ b none := (norm_nonneg b).trans (hBb b hb)
    have hy' : a none + b none < R := by simpa using hy
    exact ⟨a, ⟨ha, by rw [mem_closedBall_zero_iff]; linarith [hAb a ha]⟩, b,
      ⟨hb, by rw [mem_closedBall_zero_iff]; linarith [hBb b hb]⟩, rfl⟩
  have h2 : z ∈ closure ((A ∩ Metric.closedBall 0 R) + (B ∩ Metric.closedBall 0 R)) :=
    closure_mono hsub h1
  rw [hP.isClosed.closure_eq] at h2
  obtain ⟨a, ha, b, hb, rfl⟩ := h2
  exact ⟨a, ha.1, b, hb.1, rfl⟩

/-! ### the recursively defined cones -/

def Cl {ι : Type} (K : Set (Option ι → ℝ)) : List ι → Set (Option ι → ℝ)
  | [] => K
  | i :: l => (Cl K l ∩ H i) + (Cl K l ∩ G i)

theorem norm_le_of_Q [Fintype ι] {a : Option ι → ℝ} (ha : a ∈ (Q : Set (Option ι → ℝ))) :
    ‖a‖ ≤ a none := by
  obtain ⟨h0, hb⟩ := Q_bounds ha
  refine (pi_norm_le_iff_of_nonneg h0).2 (fun j => ?_)
  rw [Real.norm_eq_abs]
  cases j with
  | none => exact le_of_eq (abs_of_nonneg h0)
  | some i => rw [abs_of_nonneg (hb i).1]; exact (hb i).2

theorem Cl_props [Fintype ι] {K : Set (Option ι → ℝ)} (hK : IsConvexCone K) (hKc : IsClosed K)
    (hKQ : K ⊆ Q) (l : List ι) :
    IsClosed (Cl K l) ∧ Cl K l ⊆ K ∧ (0 : Option ι → ℝ) ∈ Cl K l ∧
      (∀ x ∈ Cl K l, ∀ y ∈ Cl K l, x + y ∈ Cl K l) ∧
      ∀ c : ℝ, 0 ≤ c → ∀ x ∈ Cl K l, c • x ∈ Cl K l := by
  induction l with
  | nil =>
    obtain ⟨⟨x0, hx0⟩, hadd, hsmul⟩ := hK
    refine ⟨hKc, fun x hx => hx, ?_, hadd, hsmul⟩
    have := hsmul 0 le_rfl x0 hx0
    have h00 : (0 : Option ι → ℝ) ∈ K := by simpa using this
    exact h00
  | cons i l ih =>
    obtain ⟨hcl, hsub, h0, hadd, hsmul⟩ := ih
    have hH : IsClosed (H i : Set (Option ι → ℝ)) :=
      isClosed_eq (continuous_apply (some i)) continuous_const
    have hG : IsClosed (G i : Set (Option ι → ℝ)) :=
      isClosed_eq (continuous_apply (some i)) (continuous_apply none)
    have hA : IsClosed (Cl K l ∩ H i) := hcl.inter hH
    have hB : IsClosed (Cl K l ∩ G i) := hcl.inter hG
    have hAb : ∀ a ∈ Cl K l ∩ H i, ‖a‖ ≤ a none := fun a ha => norm_le_of_Q (hKQ (hsub ha.1))
    have hBb : ∀ a ∈ Cl K l ∩ G i, ‖a‖ ≤ a none := fun a ha => norm_le_of_Q (hKQ (hsub ha.1))
    refine ⟨add_closed hA hB hAb hBb, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨a, ha, b, hb, rfl⟩
      exact hK.2.1 a (hsub ha.1) b (hsub hb.1)
    · exact ⟨0, ⟨h0, by simp [H]⟩, 0, ⟨h0, by simp [G]⟩, by simp⟩
    · rintro _ ⟨a, ha, b, hb, rfl⟩ _ ⟨a', ha', b', hb', rfl⟩
      refine ⟨a + a', ⟨hadd a ha.1 a' ha'.1, ?_⟩, b + b', ⟨hadd b hb.1 b' hb'.1, ?_⟩, (add_add_add_comm a b a' b').symm⟩
      · have h1 : a (some i) = 0 := ha.2
        have h2 : a' (some i) = 0 := ha'.2
        show (a + a') (some i) = 0
        simp [h1, h2]
      · have h1 : b (some i) = b none := hb.2
        have h2 : b' (some i) = b' none := hb'.2
        show (b + b') (some i) = (b + b') none
        simp [h1, h2]
    · rintro c hc _ ⟨a, ha, b, hb, rfl⟩
      refine ⟨c • a, ⟨hsmul c hc a ha.1, ?_⟩, c • b, ⟨hsmul c hc b hb.1, ?_⟩, by rw [smul_add]⟩
      · have h1 : a (some i) = 0 := ha.2
        show (c • a) (some i) = 0
        simp [h1]
      · have h1 : b (some i) = b none := hb.2
        show (c • b) (some i) = (c • b) none
        simp [h1]

/-! ### faces of a generated cone -/

theorem cone_face {S : Set (Option ι → ℝ)} (φ : (Option ι → ℝ) → ℝ)
    (hadd : ∀ x y, φ (x + y) = φ x + φ y) (hsmul : ∀ (c : ℝ) x, φ (c • x) = c * φ x)
    (h0 : φ 0 = 0)
    (hφ : ∀ p ∈ S, 0 ≤ φ p) {a : Option ι → ℝ} (ha : a ∈ cone S) :
    0 ≤ φ a ∧ (φ a = 0 → a ∈ cone (S ∩ {p | φ p = 0})) := by
  refine cone_induction (P := fun a => 0 ≤ φ a ∧ (φ a = 0 → a ∈ cone (S ∩ {p | φ p = 0})))
    ?_ ?_ ?_ ?_ ha
  · intro p hp
    exact ⟨hφ p hp, fun h => subset_cone _ ⟨hp, h⟩⟩
  · exact ⟨by rw [h0], fun _ => zero_mem_cone _⟩
  · rintro x y ⟨hx0, hx⟩ ⟨hy0, hy⟩
    refine ⟨by rw [hadd]; linarith, fun h => ?_⟩
    rw [hadd] at h
    exact add_mem_cone (hx (by linarith)) (hy (by linarith))
  · rintro c hc x ⟨hx0, hx⟩
    refine ⟨by rw [hsmul]; exact mul_nonneg hc hx0, fun h => ?_⟩
    rw [hsmul] at h
    rcases mul_eq_zero.1 h with h | h
    · subst h
      simpa using zero_mem_cone _
    · exact smul_mem_cone hc (hx h)

theorem K_sub_cone {K : Set (Option ι → ℝ)} (hK : IsConvexCone K) (hKQ : K ⊆ Q) :
    K ⊆ cone (K ∩ Fbar (∅ : Finset ι)) := by
  intro x hx
  obtain ⟨h0, hb⟩ := Q_bounds (hKQ hx)
  rcases h0.eq_or_lt with h | h
  · have hx0 : x = 0 := by
      funext j
      cases j with
      | none => exact h.symm
      | some i => 
        have := hb i
        show x (some i) = 0
        linarith [this.1, this.2]
    rw [hx0]
    exact zero_mem_cone _
  · have hxe : x = x none • ((x none)⁻¹ • x) := by
      rw [smul_smul, mul_inv_cancel₀ h.ne', one_smul]
    rw [hxe]
    refine smul_mem_cone h.le (subset_cone _ ⟨hK.2.2 _ (inv_nonneg.2 h.le) x hx, ?_, ?_, ?_⟩)
    · simp [h.ne']
    · intro i
      have := hb i
      simp only [Pi.smul_apply, smul_eq_mul]
      refine ⟨mul_nonneg (inv_nonneg.2 h.le) this.1, ?_⟩
      rw [inv_mul_le_iff₀ h]
      linarith [this.2]
    · intro i hi
      simp at hi

theorem Cl_sub_cone [Fintype ι] [DecidableEq ι] {K : Set (Option ι → ℝ)} (hK : IsConvexCone K)
    (hKQ : K ⊆ Q) (l : List ι) : Cl K l ⊆ cone (K ∩ Fbar l.toFinset) := by
  induction l with
  | nil => simpa [Cl] using K_sub_cone hK hKQ
  | cons i l ih =>
    rintro _ ⟨a, ha, b, hb, rfl⟩
    have ha' := ih ha.1
    have hb' := ih hb.1
    refine add_mem_cone ?_ ?_
    · have := (cone_face (fun p => p (some i)) (fun x y => rfl) (fun c x => rfl) rfl
        (fun p hp => (hp.2.2.1 i).1) ha').2
        (by simpa [H] using ha.2)
      refine cone_mono ?_ this
      rintro p ⟨⟨hpK, hp0, hpc, hpT⟩, hpi⟩
      have hpi' : p (some i) = 0 := hpi
      refine ⟨hpK, hp0, hpc, ?_⟩
      intro j hj
      rw [List.toFinset_cons, Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · exact Or.inl hpi'
      · exact hpT j hj
    · have := (cone_face (fun p => p none - p (some i))
        (fun x y => by simp only [Pi.add_apply]; ring)
        (fun c x => by simp only [Pi.smul_apply, smul_eq_mul]; ring) (by simp)
        (fun p hp => by
          have h1 := (hp.2.2.1 i).2
          have h2 := hp.2.1
          show 0 ≤ p none - p (some i)
          linarith) hb').2
        (by
          have h1 : b (some i) = b none := hb.2
          show b none - b (some i) = 0
          rw [h1]; ring)
      refine cone_mono ?_ this
      rintro p ⟨⟨hpK, hp0, hpc, hpT⟩, hpi⟩
      have hpi' : p none - p (some i) = 0 := hpi
      refine ⟨hpK, hp0, hpc, ?_⟩
      intro j hj
      rw [List.toFinset_cons, Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · right; linarith
      · exact hpT j hj

/-! ### the upper bound -/

theorem Niter_sub_Cl [Fintype ι] [DecidableEq ι] {K : Set (Option ι → ℝ)} (hK : IsConvexCone K)
    (hKc : IsClosed K) (hKQ : K ⊆ Q) (l : List ι) : Niter l.length K ⊆ Cl K l := by
  induction l with
  | nil => exact fun x hx => hx
  | cons i l ih =>
    intro x hx
    have hx' : x ∈ N1 (Niter l.length K) := hx
    obtain ⟨Y, ⟨hsymm, hdiag, hdual⟩, rfl⟩ := hx'
    obtain ⟨hcl, -, h0, hadd, hsmul⟩ := Cl_props hK hKc hKQ l
    have hei : (Pi.single (some i) (1:ℝ) : Option ι → ℝ) ∈ dualCone (Q : Set (Option ι → ℝ)) := by
      intro x hx
      have := (Q_bounds hx).2 i
      simp only [single_dotProduct]
      linarith [this.1]
    have he0i : (Pi.single none (1:ℝ) - Pi.single (some i) (1:ℝ) : Option ι → ℝ) ∈
        dualCone (Q : Set (Option ι → ℝ)) := by
      intro x hx
      have := (Q_bounds hx).2 i
      simp only [sub_dotProduct, single_dotProduct]
      linarith [this.2]
    have hdual' : ∀ u ∈ dualCone (Cl K l), ∀ v ∈ dualCone (Q : Set (Option ι → ℝ)),
        0 ≤ u ⬝ᵥ (Y *ᵥ v) := fun u hu v hv =>
      hdual u (fun x hx => hu x (ih hx)) v hv
    have hB : Y *ᵥ Pi.single (some i) (1:ℝ) ∈ Cl K l :=
      bipolar h0 hadd hsmul hcl (fun u hu => hdual' u hu _ hei)
    have hA : Y *ᵥ (Pi.single none (1:ℝ) - Pi.single (some i) (1:ℝ)) ∈ Cl K l :=
      bipolar h0 hadd hsmul hcl (fun u hu => hdual' u hu _ he0i)
    have hdi : Y (some i) (some i) = Y none (some i) := hdiag i
    have hs : Y (some i) none = Y none (some i) := by
      have := hsymm.apply none (some i)
      exact this
    refine ⟨Y *ᵥ (Pi.single none (1:ℝ) - Pi.single (some i) (1:ℝ)), ⟨hA, ?_⟩,
      Y *ᵥ Pi.single (some i) (1:ℝ), ⟨hB, ?_⟩, ?_⟩
    · show (Y *ᵥ (Pi.single none (1:ℝ) - Pi.single (some i) (1:ℝ))) (some i) = 0
      simp [Matrix.mulVec_sub, hs, hdi]
    · show (Y *ᵥ Pi.single (some i) (1:ℝ)) (some i) = (Y *ᵥ Pi.single (some i) (1:ℝ)) none
      simp [hdi]
    · show _ + _ = _
      rw [← Matrix.mulVec_add]
      congr 1
      abel

/-! ### the lower bound -/

theorem hull01_sub_Niter [Fintype ι] [DecidableEq ι] {K : Set (Option ι → ℝ)}
    (hK : IsConvexCone K) (hKQ : K ⊆ Q) (t : ℕ) : hull01 K ⊆ Niter t K := by
  induction t with
  | zero =>
    intro x hx
    have hx' : x ∈ cone {x : Option ι → ℝ | x ∈ K ∧ IsZeroOne x} := hx
    refine cone_induction (P := fun x => x ∈ K) (fun y hy => hy.1) ?_ (fun x y hx hy => hK.2.1 x hx y hy)
      (fun c hc x hx => hK.2.2 c hc x hx) hx'
    obtain ⟨x0, hx0⟩ := hK.1
    have := hK.2.2 0 le_rfl x0 hx0
    simpa using this
  | succ t ih =>
    intro x hx
    have hx' : x ∈ cone {x : Option ι → ℝ | x ∈ K ∧ IsZeroOne x} := hx
    show x ∈ N (Niter t K) Q
    refine cone_induction (P := fun x => x ∈ N (Niter t K) (Q : Set (Option ι → ℝ))) ?_ ?_ ?_ ?_ hx'
    · rintro p ⟨hpK, hp01⟩
      have hpQ := Q_bounds (hKQ hpK)
      have hpN : p ∈ Niter t K := ih (subset_cone _ ⟨hpK, hp01⟩)
      have hxx : ∀ j, p j * p none = p j := by
        intro j
        rcases hp01 none with h0 | h0
        · have : p j = 0 := by
            cases j with
            | none => exact h0
            | some i => linarith [(hpQ.2 i).1, (hpQ.2 i).2]
          rw [this]; ring
        · rw [h0]; ring
      refine ⟨Matrix.vecMulVec p p, ⟨?_, ?_, ?_⟩, ?_⟩
      · ext i j
        simp [Matrix.vecMulVec, mul_comm]
      · intro i
        simp only [Matrix.vecMulVec_apply]
        rcases hp01 (some i) with h | h
        · rw [h]; ring
        · have := hxx (some i)
          rw [h] at this ⊢
          linarith
      · intro u hu v hv
        have hvv : Matrix.vecMulVec p p *ᵥ v = (p ⬝ᵥ v) • p := by
          ext k
          simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
            Finset.sum_mul]
          exact Finset.sum_congr rfl (fun j _ => by ring)
        rw [hvv, dotProduct_smul, smul_eq_mul]
        have h1 : 0 ≤ v ⬝ᵥ p := hv p (hKQ hpK)
        have h2 : 0 ≤ u ⬝ᵥ p := hu p hpN
        rw [dotProduct_comm p v]
        exact mul_nonneg h1 h2
      · funext j
        simp [Matrix.vecMulVec_apply, hxx j]
    · exact ⟨0, ⟨by simp [Matrix.IsSymm], by simp, by simp⟩, Matrix.zero_mulVec _⟩
    · rintro x y ⟨Y1, ⟨s1, d1, u1⟩, e1⟩ ⟨Y2, ⟨s2, d2, u2⟩, e2⟩
      refine ⟨Y1 + Y2, ⟨s1.add s2, fun i => ?_, fun u hu v hv => ?_⟩, ?_⟩
      · simp [Matrix.add_apply, d1 i, d2 i]
      · rw [Matrix.add_mulVec, dotProduct_add]
        exact add_nonneg (u1 u hu v hv) (u2 u hu v hv)
      · rw [Matrix.add_mulVec, e1, e2]
    · rintro c hc x ⟨Y, ⟨s, d, u⟩, e⟩
      refine ⟨c • Y, ⟨s.smul c, fun i => ?_, fun w hw v hv => ?_⟩, ?_⟩
      · simp [d i]
      · rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
        exact mul_nonneg hc (u w hw v hv)
      · rw [Matrix.smul_mulVec, e]

end LS32d53bf7

open LovaszSchrijver.IntegerHull in
theorem solution {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : Set (Option ι → ℝ)) (hK : IsConvexCone K) (hKc : IsClosed K) (hKQ : K ⊆ Q) :
    Niter (Fintype.card ι) K = hull01 K := by
  apply Set.Subset.antisymm
  · intro x hx
    have hl : (Finset.univ : Finset ι).toList.length = Fintype.card ι := by simp
    have h1 := LS32d53bf7.Niter_sub_Cl hK hKc hKQ (Finset.univ : Finset ι).toList
    rw [hl] at h1
    have h2 := LS32d53bf7.Cl_sub_cone hK hKQ (Finset.univ : Finset ι).toList (h1 hx)
    rw [Finset.toList_toFinset] at h2
    refine LS32d53bf7.cone_mono ?_ h2
    rintro p ⟨hpK, hp0, -, hpT⟩
    refine ⟨hpK, fun j => ?_⟩
    cases j with
    | none => exact Or.inr hp0
    | some i => exact hpT i (Finset.mem_univ i)
  · exact LS32d53bf7.hull01_sub_Niter hK hKQ _

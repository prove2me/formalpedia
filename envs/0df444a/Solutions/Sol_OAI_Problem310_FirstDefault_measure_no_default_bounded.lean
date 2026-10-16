-- Prove2me | solution 1 for OAI.Problem310.FirstDefault.measure_no_default_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:53:13.072191+00:00
-- url     : https://prove2.me/submissions/41c4cdfb-0995-472e-af64-2a9896ca987e

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/FirstDefault.lean:L205-L237
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.FirstDefault.measure_no_default_bounded. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterRouteExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ExceptionalCenters
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFailureBound
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefault

-- ---- from OAI.MeasureTheory.DyadicAvoidance.FirstDefault ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

universe u_Ω

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Problem310.FirstDefault

lemma address_injective {M d : ℕ} (f : Path M d) :
    Function.Injective (address f) := by
  rintro ⟨k, i⟩ ⟨l, j⟩ h
  have hlen := congrArg (fun a : Address M => a.1.length) h
  simp only [address, pathPrefix, List.length_ofFn] at hlen
  have hkl : k = l := Fin.ext hlen
  subst l
  have hij := congrArg (fun a : Address M => a.2.val) h
  simp only [address] at hij
  have : i = j := Fin.ext hij
  subst j
  rfl

lemma measure_cylinder_of_local {M d : ℕ} {Ω : Type u_Ω} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Address M → Ω → Bool) (f : Path M d)
    (hi : iIndepFun (fun i : Tests f => S (address f i)) μ)
    (hfair : ∀ i : Tests f, ∀ b, μ (S (address f i) ⁻¹' {b}) = (2 : ENNReal)⁻¹) :
    μ (cylinder S f) = ∏ k : Fin d, ((2 : ENNReal)⁻¹) ^ ((f k).val + 1) := by
  classical
  have h := hi.measure_inter_preimage_eq_mul Finset.univ
    (sets := fun i : Tests f => {requiredBit f i}) (by intro i _; exact measurableSet_singleton _)
  have heq : (⋂ i : Tests f, ⋂ (_ : i ∈ Finset.univ),
      S (address f i) ⁻¹' {requiredBit f i}) = cylinder S f := by
    ext ω
    simp [cylinder]
  rw [heq] at h
  rw [h]
  simp only [hfair]
  rw [Fintype.prod_sigma]
  simp

lemma cylinder_disjoint_of_prefix {M d : ℕ} {Ω : Type u_Ω}
    (S : Address M → Ω → Bool) (f g : Path M d) (k : Fin d)
    (hprefix : pathPrefix f k = pathPrefix g k) (hlt : f k < g k) :
    Disjoint (cylinder S f) (cylinder S g) := by
  apply Set.disjoint_left.mpr
  intro ω hf hg
  have h1 := hf ⟨k, ⟨(f k).val, Nat.lt_succ_self _⟩⟩
  have h2 := hg ⟨k, ⟨(f k).val, lt_trans hlt (Nat.lt_succ_self _)⟩⟩
  have ha : (address f ⟨k, ⟨(f k).val, Nat.lt_succ_self _⟩⟩) =
      address g ⟨k, ⟨(f k).val, lt_trans hlt (Nat.lt_succ_self _)⟩⟩ := by
    simp only [address, hprefix]
  have hb1 : requiredBit f ⟨k, ⟨(f k).val, Nat.lt_succ_self _⟩⟩ = true := by
    simp [requiredBit]
  have hb2 : requiredBit g
      ⟨k, ⟨(f k).val, lt_trans hlt (Nat.lt_succ_self _)⟩⟩ = false := by
    have hne : (f k).val ≠ (g k).val := Nat.ne_of_lt hlt
    simp [requiredBit, hne]
  rw [hb1, ha] at h1
  rw [hb2, h1] at h2
  cases h2

lemma cylinders_pairwiseDisjoint {M d : ℕ} {Ω : Type u_Ω}
    (S : Address M → Ω → Bool) : Pairwise (fun f g : Path M d => Disjoint (cylinder S f) (cylinder S g)) := by
  classical
  intro f g hfg
  have hex : ∃ k, f k ≠ g k := by
    by_contra! h
    exact hfg (funext h)
  let T : Finset (Fin d) := Finset.univ.filter fun k => f k ≠ g k
  have hT : T.Nonempty := by
    obtain ⟨k, hk⟩ := hex
    exact ⟨k, by simp [T, hk]⟩
  obtain ⟨k, hk, hmin⟩ := Finset.exists_min_image T (fun i => i) hT
  have hkne : f k ≠ g k := (Finset.mem_filter.mp hk).2
  have hearlier : ∀ j : Fin d, j < k → f j = g j := by
    intro j hj
    by_contra hne
    exact (not_le_of_gt hj) (hmin j (by simp [T, hne]))
  have hprefix : pathPrefix f k = pathPrefix g k := by
    unfold pathPrefix
    congr 1
    funext j
    rw [hearlier ⟨j.val, lt_trans j.isLt k.isLt⟩ j.isLt]
  rcases lt_or_gt_of_ne hkne with hlt | hgt
  · exact cylinder_disjoint_of_prefix S f g k hprefix hlt
  · exact (cylinder_disjoint_of_prefix S g f k hprefix.symm hgt).symm

lemma measurableSet_cylinder {M d : ℕ} {Ω : Type u_Ω} [MeasurableSpace Ω]
    (S : Address M → Ω → Bool) (hS : ∀ a, Measurable (S a)) (f : Path M d) :
    MeasurableSet (cylinder S f) := by
  simp only [cylinder, Set.ofPred_forall]
  exact MeasurableSet.iInter fun i => (hS _) (measurableSet_singleton _)

lemma sum_geometric_weights (M : ℕ) :
    (∑ i : Fin M, ((2 : ENNReal)⁻¹) ^ (i.val + 1)) =
      1 - ((2 : ENNReal)⁻¹) ^ M := by
  have hadd (n : ℕ) :
      (∑ i : Fin n, ((2 : ENNReal)⁻¹) ^ (i.val + 1)) +
        ((2 : ENNReal)⁻¹) ^ n = 1 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      have hq : (2 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹ = 1 := ENNReal.inv_two_add_inv_two
      calc
        (∑ i : Fin n, ((2 : ENNReal)⁻¹) ^ (i.val + 1)) +
            ((2 : ENNReal)⁻¹) ^ (n + 1) + ((2 : ENNReal)⁻¹) ^ (n + 1) =
          (∑ i : Fin n, ((2 : ENNReal)⁻¹) ^ (i.val + 1)) +
            ((2 : ENNReal)⁻¹) ^ n * ((2 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹) := by
              rw [pow_succ]
              ring
        _ = 1 := by rw [hq, mul_one]; exact ih
  exact ENNReal.eq_sub_of_add_eq (by finiteness) (hadd M)

/-- Local independence suffices: only the finitely many addresses on each
prescribed path are required to be independent and fair. -/
theorem measure_no_default_of_local {M d : ℕ} {Ω : Type u_Ω} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Address M → Ω → Bool)
    (hS : ∀ a, Measurable (S a))
    (hIndep : ∀ f : Path M d, iIndepFun (fun i : Tests f => S (address f i)) μ)
    (hfair : ∀ f : Path M d, ∀ i : Tests f, ∀ b,
      μ (S (address f i) ⁻¹' {b}) = (2 : ENNReal)⁻¹) :
    μ (⋃ f : Path M d, cylinder S f) =
      (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d := by
  classical
  rw [measure_iUnion (cylinders_pairwiseDisjoint S) (measurableSet_cylinder S hS),
    tsum_fintype]
  simp_rw [measure_cylinder_of_local μ S _ (hIndep _) (hfair _)]
  calc
    _ = (∑ i : Fin M, ((2 : ENNReal)⁻¹) ^ (i.val + 1)) ^ d :=
      (Fintype.sum_pow (fun i : Fin M => ((2 : ENNReal)⁻¹) ^ (i.val + 1)) d).symm
    _ = _ := by rw [sum_geometric_weights]

lemma boundedAddress_injective {M d : ℕ} (f : Path M d) :
    Function.Injective (boundedAddress f) := by
  intro i j h
  exact address_injective f (congrArg Subtype.val h)

/-- Finite-tree version: no randomness outside nodes of depth less than `d`
is assumed. This is the interface for the actual finite table model. -/
theorem measure_no_default_bounded {M d : ℕ} {Ω : Type u_Ω} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : BoundedAddress M d → Ω → Bool)
    (hS : ∀ a, Measurable (S a)) (hIndep : iIndepFun S μ)
    (hfair : ∀ a b, μ (S a ⁻¹' {b}) = (2 : ENNReal)⁻¹) :
    μ (⋃ f : Path M d,
      {ω | ∀ i : Tests f, S (boundedAddress f i) ω = requiredBit f i}) =
      (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d := by
  classical
  let S' : Address M → Ω → Bool := fun a ω =>
    if h : a.1.length < d then S ⟨a, h⟩ ω else false
  have heval (f : Path M d) (i : Tests f) :
      S' (address f i) = S (boundedAddress f i) := by
    funext ω
    simp only [S', dite_eq_left (address_length_lt f i), boundedAddress]
  have hS' : ∀ a, Measurable (S' a) := by
    intro a
    dsimp only [S']
    split
    · exact hS _
    · exact measurable_const
  have hi : ∀ f : Path M d, iIndepFun (fun i : Tests f => S' (address f i)) μ := by
    intro f
    simp_rw [heval]
    exact hIndep.precomp (boundedAddress_injective f)
  have hf : ∀ f : Path M d, ∀ i : Tests f, ∀ b,
      μ (S' (address f i) ⁻¹' {b}) = (2 : ENNReal)⁻¹ := by
    intro f i b
    rw [heval]
    exact hfair _ b
  have h := measure_no_default_of_local μ S' hS' hi hf
  simpa only [cylinder, heval] using h

end Problem310.FirstDefault

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.FirstDefault
open MeasureTheory ProbabilityTheory
open scoped BigOperators


theorem solution.{u_Ω} : type_of% @_root_.OAI.Problem310.FirstDefault.measure_no_default_bounded.{u_Ω} := @_root_.OAI.Problem310.FirstDefault.measure_no_default_bounded.{u_Ω}

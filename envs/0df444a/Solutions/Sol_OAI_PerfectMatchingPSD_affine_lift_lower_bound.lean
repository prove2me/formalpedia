-- Prove2me | solution 1 for OAI.PerfectMatchingPSD.affine_lift_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T14:52:05.309895+00:00
-- url     : https://prove2.me/submissions/988dc22d-83db-4425-b67a-7c102c6528d8

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/AffineLift.lean:L11-L22
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.PerfectMatchingPSD.affine_lift_lower_bound.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_PerfectMatchingPSD_affine_lift_lower_bound) verbatim and is proved by it.
import Mathlib
import Definitions.Def_MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PSDEvaluation
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Model
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EquivariantCompression__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialSpaces__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_FiberAverages__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ScalarSmoothing__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeMonomials__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PartialColorings__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableCoordinates__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TablePolynomials__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PermutationSmoothing__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingFibers__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GlobalGeometry__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_AdmissibleTables__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CutGeometry__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellAverages__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SequentialTests__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatrixAverages__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialInterpolation__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatrixInterpolation__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GoodCells__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellDecoder__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_AffineSlacks
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingConversion__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Padding__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Parameters__MatchingAffineLift
import Theorems.Thm_OAI_AffinePSD_affine_slack_certificate
import Theorems.Thm_OAI_PerfectMatchingPSD_crossingCount_fromPairing
import Theorems.Thm_OAI_PerfectMatchingPSD_slackAffine_vertex

-- ---- from OAI.Combinatorics.MatchingPSD.Involutions ----
namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing

section CommutingInvolutions

variable {ι : Type u_1} {V : Type u_2} [AddCommGroup V] [Module ℝ V]

lemma eigen_add_commuting (A B : Module.End ℝ V) (hAB : Commute A B)
    (v : V) (c : ℝ) (hv : A v = c • v) :
    A (v + B v) = c • (v + B v) := by
  have hc : A (B v) = B (A v) := congrArg (fun f : Module.End ℝ V => f v) hAB.eq
  rw [map_add, hv, hc, hv, map_smul, smul_add]

lemma eigen_sub_commuting (A B : Module.End ℝ V) (hAB : Commute A B)
    (v : V) (c : ℝ) (hv : A v = c • v) :
    A (v - B v) = c • (v - B v) := by
  have hc : A (B v) = B (A v) := congrArg (fun f : Module.End ℝ V => f v) hAB.eq
  rw [map_sub, hv, hc, hv, map_smul, smul_sub]

lemma simultaneous_sign_eigenvector_on (A : ι → Module.End ℝ V)
    (hcomm : ∀ i j, Commute (A i) (A j))
    (hinv : ∀ i v, A i (A i v) = v)
    (W : Submodule ℝ V) (hstable : ∀ i v, v ∈ W → A i v ∈ W)
    (hne : ∃ v ∈ W, v ≠ 0) (s : Finset ι) :
    ∃ (χ : ι → ℝ) (v : V), v ∈ W ∧ v ≠ 0 ∧
      ∀ i ∈ s, (χ i = 1 ∨ χ i = -1) ∧ A i v = χ i • v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨v, hv, hv0⟩ := hne
    exact ⟨fun _ => 1, v, hv, hv0, by simp⟩
  | @insert i s his ih =>
    obtain ⟨χ, v, hv, hv0, heig⟩ := ih
    by_cases hp : v + A i v = 0
    · have hm : v - A i v ≠ 0 := by
        intro hm
        have htwo : (2 : ℝ) • v = 0 := by
          rw [two_smul]
          linear_combination (norm := abel) hp + hm
        exact hv0 ((smul_eq_zero.mp htwo).resolve_left (by norm_num))
      refine ⟨Function.update χ i (-1), v - A i v,
        W.sub_mem hv (hstable i v hv), hm, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simp only [Function.update_self, neg_smul, one_smul]
        refine ⟨by simp, ?_⟩
        rw [map_sub, hinv]
        abel
      · have hji : j ≠ i := by intro h; subst j; exact his hj
        rw [Function.update_of_ne hji]
        exact ⟨(heig j hj).1, eigen_sub_commuting (A j) (A i) (hcomm j i)
          v (χ j) (heig j hj).2⟩
    · refine ⟨Function.update χ i 1, v + A i v,
        W.add_mem hv (hstable i v hv), hp, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simp only [Function.update_self, one_smul]
        refine ⟨by simp, ?_⟩
        rw [map_add, hinv, add_comm]
      · have hji : j ≠ i := by intro h; subst j; exact his hj
        rw [Function.update_of_ne hji]
        exact ⟨(heig j hj).1, eigen_add_commuting (A j) (A i) (hcomm j i)
          v (χ j) (heig j hj).2⟩

lemma simultaneous_sign_eigenvector [Fintype ι] (A : ι → Module.End ℝ V)
    (hcomm : ∀ i j, Commute (A i) (A j))
    (hinv : ∀ i v, A i (A i v) = v)
    (W : Submodule ℝ V) (hstable : ∀ i v, v ∈ W → A i v ∈ W)
    (hne : ∃ v ∈ W, v ≠ 0) :
    ∃ (χ : ι → ℝ) (v : V), v ∈ W ∧ v ≠ 0 ∧
      ∀ i, (χ i = 1 ∨ χ i = -1) ∧ A i v = χ i • v := by
  simpa using simultaneous_sign_eigenvector_on A hcomm hinv W hstable hne Finset.univ

lemma simultaneous_sign_eigenvector_preserving [Fintype ι]
    (A : ι → Module.End ℝ V) (hcomm : ∀ i j, Commute (A i) (A j))
    (hinv : ∀ i v, A i (A i v) = v)
    (W : Submodule ℝ V) (hstable : ∀ i v, v ∈ W → A i v ∈ W)
    (s : Finset ι) (χ : ι → ℝ)
    (v : V) (hv : v ∈ W) (hv0 : v ≠ 0) (he : ∀ i ∈ s, A i v = χ i • v) :
    ∃ (ψ : ι → ℝ) (w : V), w ∈ W ∧ w ≠ 0 ∧
      (∀ i, (ψ i = 1 ∨ ψ i = -1) ∧ A i w = ψ i • w) ∧
      ∀ i ∈ s, ψ i = χ i := by
  let U : Submodule ℝ V :=
    { carrier := {w | w ∈ W ∧ ∀ i ∈ s, A i w = χ i • w}
      zero_mem' := by simp
      add_mem' := by
        rintro a b ⟨ha, hea⟩ ⟨hb, heb⟩
        exact ⟨W.add_mem ha hb, fun i hi => by rw [map_add, hea i hi, heb i hi, smul_add]⟩
      smul_mem' := by
        rintro c a ⟨ha, hea⟩
        exact ⟨W.smul_mem c ha, fun i hi => by rw [map_smul, hea i hi, smul_comm]⟩ }
  have hU (j : ι) (w : V) (hw : w ∈ U) : A j w ∈ U := by
    refine ⟨hstable j w hw.1, ?_⟩
    intro i hi
    have hc := congrArg (fun f : Module.End ℝ V => f w) (hcomm i j).eq
    change A i (A j w) = A j (A i w) at hc
    rw [hc, hw.2 i hi, map_smul]
  obtain ⟨ψ, w, hw, hw0, hew⟩ := simultaneous_sign_eigenvector A hcomm hinv U hU
    ⟨v, ⟨hv, he⟩, hv0⟩
  refine ⟨ψ, w, hw.1, hw0, hew, ?_⟩
  intro i hi
  exact smul_left_injective ℝ hw0 ((hew i).2.symm.trans (hw.2 i hi))

lemma independent_eigenprofiles {κ : Type u_3} (A : ι → Module.End ℝ V)
    (hcomm : ∀ i j, Commute (A i) (A j)) (χ : κ → ι → ℝ)
    (hinj : Function.Injective χ) (v : κ → V) (hv : ∀ k, v k ≠ 0)
    (heig : ∀ k i, A i (v k) = χ k i • v k) : LinearIndependent ℝ v := by
  have hi := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo A
    (fun i j c => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) c)
  apply (hi.comp hinj).linearIndependent _ _ hv
  intro k
  change v k ∈ ⨅ i, (A i).maxGenEigenspace (χ k i)
  rw [Submodule.mem_iInf]
  intro i
  exact Module.End.eigenspace_le_maxGenEigenspace
    (Module.End.mem_eigenspace_iff.mpr (heig k i))

lemma binomial_le_finrank_of_eigenvector_mem [Fintype ι] [DecidableEq ι] [FiniteDimensional ℝ V]
    (A : ι → Module.End ℝ V) (hcomm : ∀ i j, Commute (A i) (A j))
    (P : Equiv.Perm ι → V ≃ₗ[ℝ] V)
    (hconj : ∀ p i v, A (p i) (P p v) = P p (A i v))
    (W : Submodule ℝ V) (hW : ∀ p v, v ∈ W → P p v ∈ W)
    (s : Finset ι) (v : V) (hvW : v ∈ W) (hv : v ≠ 0)
    (heig : ∀ i, A i v = (if i ∈ s then (-1 : ℝ) else 1) • v) :
    (Fintype.card ι).choose s.card ≤ Module.finrank ℝ W := by
  classical
  let T := ↥((Finset.univ : Finset ι).powersetCard s.card)
  have hp (t : T) : ∃ p : Equiv.Perm ι, s.map p.toEmbedding = t.1 :=
    Equiv.Perm.exists_map_finset_eq s t.1
      (Finset.mem_powersetCard.mp t.2).2.symm
  choose p hp using hp
  let χ (t : T) (i : ι) : ℝ := if i ∈ t.1 then -1 else 1
  have hχ : Function.Injective χ := by
    intro t u h
    apply Subtype.ext
    ext i
    have hh := congrFun h i
    dsimp [χ] at hh
    by_cases ht : i ∈ t.1 <;> by_cases hu : i ∈ u.1 <;> simp_all <;> norm_num at hh
  have hprof (t : T) (i : ι) : A i (P (p t) v) = χ t i • P (p t) v := by
    have hi : (p t).symm i ∈ s ↔ i ∈ t.1 := by
      rw [← hp t]
      simp
    by_cases hii : i ∈ t.1 <;>
      simpa [heig, χ, hi, hii] using hconj (p t) ((p t).symm i) v
  have hli := independent_eigenprofiles A hcomm χ hχ
    (fun t => P (p t) v) (fun t => by simpa using hv) hprof
  let vw (t : T) : W := ⟨P (p t) v, hW (p t) v hvW⟩
  have hliw : LinearIndependent ℝ vw := LinearIndependent.of_comp W.subtype hli
  have hc := hliw.fintype_card_le_finrank
  simpa only [T, Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ] using hc

end CommutingInvolutions
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.EdgeProducts ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

universe u_1 u_2 u_3 u_4

namespace MatchingSmoothing
variable {E : Type u_1} {X : Type u_2}

lemma lowDegree_mono (x : E → X → ℝ) {d e : ℕ} (h : d ≤ e) :
    lowDegree x d ≤ lowDegree x e := by
  apply Submodule.span_mono
  rintro f ⟨l, hl, hf⟩
  exact ⟨l, hl.trans h, hf⟩

lemma one_mem_lowDegree (x : E → X → ℝ) (d : ℕ) : (1 : X → ℝ) ∈ lowDegree x d :=
  Submodule.subset_span ⟨[], Nat.zero_le _, rfl⟩

lemma coord_mem_lowDegree (x : E → X → ℝ) (e : E) : x e ∈ lowDegree x 1 := by
  apply Submodule.subset_span
  exact ⟨[e], by simp, by simp⟩

lemma mul_mem_lowDegree (x : E → X → ℝ) {d e : ℕ} {f g : X → ℝ}
    (hf : f ∈ lowDegree x d) (hg : g ∈ lowDegree x e) :
    f * g ∈ lowDegree x (d + e) := by
  refine Submodule.span_induction₂
    (p := fun f g _ _ => f * g ∈ lowDegree x (d + e)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hf hg
  · rintro f g ⟨l, hl, rfl⟩ ⟨m, hm, rfl⟩
    apply Submodule.subset_span
    exact ⟨l ++ m, by simpa using Nat.add_le_add hl hm, by simp⟩
  · intro g _; simp
  · intro f _; simp
  · intro f g h _ _ _ hf hg
    simpa only [add_mul] using (lowDegree x (d + e)).add_mem hf hg
  · intro f g h _ _ _ hg hh
    simpa only [mul_add] using (lowDegree x (d + e)).add_mem hg hh
  · intro r f g _ _ h
    simpa only [smul_mul_assoc] using (lowDegree x (d + e)).smul_mem r h
  · intro r f g _ _ h
    simpa only [mul_smul_comm] using (lowDegree x (d + e)).smul_mem r h

lemma prod_mem_lowDegree {ι : Type u_3} (x : E → X → ℝ) (s : Finset ι)
    (f : ι → X → ℝ) (hf : ∀ i ∈ s, f i ∈ lowDegree x 1) :
    (∏ i ∈ s, f i) ∈ lowDegree x s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one_mem_lowDegree x 0
  | @insert i s his ih =>
    rw [Finset.prod_insert his, Finset.card_insert_of_notMem his]
    have hi := hf i (Finset.mem_insert_self i s)
    have hs := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    simpa only [Nat.add_comm] using mul_mem_lowDegree x hi hs

lemma boolean_pattern_mem_lowDegree [DecidableEq E]
    (x : E → X → ℝ) (s t : Finset E) :
    (∏ e ∈ s, if e ∈ t then x e else 1 - x e) ∈ lowDegree x s.card := by
  apply prod_mem_lowDegree
  intro e _
  split_ifs
  · exact coord_mem_lowDegree x e
  · exact (lowDegree x 1).sub_mem (one_mem_lowDegree x 1) (coord_mem_lowDegree x e)

lemma mem_of_fiber_indicators {I : Type u_4} [Fintype I] [DecidableEq I]
    (θ : X → I) (f : X → ℝ) (S : Submodule ℝ (X → ℝ))
    (hf : ∀ a b, θ a = θ b → f a = f b)
    (hind : ∀ a, (fun b => if θ b = θ a then (1 : ℝ) else 0) ∈ S) : f ∈ S := by
  classical
  let g (i : I) : ℝ := if h : ∃ a, θ a = i then f h.choose else 0
  let b (i : I) : X → ℝ := fun a => if θ a = i then 1 else 0
  have hm (i : I) : g i • b i ∈ S := by
    by_cases hi : ∃ a, θ a = i
    · have hb : b i = b (θ hi.choose) := by rw [hi.choose_spec]
      rw [hb]
      exact S.smul_mem _ (hind hi.choose)
    · have hb : b i = 0 := by
        ext a
        have hn : θ a ≠ i := by intro h; exact hi ⟨a, h⟩
        simp [b, hn]
      simp [hb]
  have he : ∑ i, g i • b i = f := by
    ext a
    simp only [Finset.sum_apply, Pi.smul_apply, b, smul_eq_mul, mul_ite, mul_one, mul_zero]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have ha : ∃ c, θ c = θ a := ⟨a, rfl⟩
    dsimp [g]
    rw [dite_eq_left ha]
    exact hf ha.choose a ha.choose_spec
  rw [← he]
  exact S.sum_mem (fun i _ => hm i)

end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.Pairings ----
namespace OAI

universe u_1 u_2

namespace MatchingSmoothing
namespace Pairing
variable {α : Type u_2}

lemma cycleType_eq [Fintype α] [DecidableEq α] (M N : Pairing α) :
    M.1.cycleType = N.1.cycleType := by
  have hm := Equiv.Perm.cycleType_of_pow_prime_eq_one M.partner_sq
  have hn := Equiv.Perm.cycleType_of_pow_prime_eq_one N.partner_sq
  have hsum (P : Pairing α) : P.1.cycleType.sum = Fintype.card α := by
    rw [Equiv.Perm.sum_cycleType]
    have hs : P.1.support = Finset.univ := by
      ext a
      simp [Equiv.Perm.mem_support, P.partner_ne]
    rw [hs, Finset.card_univ]
  have hc : M.1.cycleType.card = N.1.cycleType.card := by
    have he := (hsum M).trans (hsum N).symm
    rw [hm, hn] at he
    simp only [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id] at he
    omega
  rw [hm, hn, hc]

lemma exists_relabel [Fintype α] [DecidableEq α] (M N : Pairing α) :
    ∃ p : Equiv.Perm α, relabel p M = N := by
  have h := Equiv.Perm.isConj_iff_cycleType_eq.mpr (cycleType_eq M N)
  rcases isConj_iff.mp h with ⟨p, hp⟩
  refine ⟨p, Subtype.ext ?_⟩
  exact hp

lemma exists_internal_edge_compl [Fintype α] [DecidableEq α]
    (M : Pairing α) (U : Finset α) (hU : 2 * U.card < Fintype.card α) :
    ∃ a, a ∉ U ∧ M.1 a ∉ U := by
  by_contra! h
  have hinj : Set.InjOn M.1 (↑Uᶜ : Set α) := M.1.injective.injOn
  have hmaps : ∀ a ∈ Uᶜ, M.1 a ∈ U := by simpa using h
  have hc := Finset.card_le_card_of_injOn M.1 hmaps hinj
  rw [Finset.card_compl] at hc
  have hu := Finset.card_le_univ U
  omega

lemma no_sign_on_complement [Fintype α] [DecidableEq α]
    (U : Finset α) (hU : 2 * U.card < Fintype.card α)
    (f : Pairing α → ℝ)
    (hf : ∀ a ∉ U, ∀ b ∉ U, a ≠ b → act (Equiv.swap a b) f = -f) : f = 0 := by
  ext M
  obtain ⟨a, ha, hma⟩ := exists_internal_edge_compl M U hU
  have he := congrFun (hf a ha (M.1 a) hma (M.partner_ne a).symm) M
  simp only [act_apply, Equiv.swap_inv, relabel_swap_partner, Pi.neg_apply] at he
  dsimp
  linarith

lemma align_partners [Fintype α] [DecidableEq α]
    (U : Finset α) (M N : Pairing α) (hMN : SameInternal U M N) :
    ∃ p : Equiv.Perm α, (∀ a ∈ U, p a = a) ∧
      ∀ a ∈ U, (relabel p M).1 a = N.1 a := by
  classical
  let S := {a : α // a ∈ U ∧ M.1 a ∉ U}
  have hnout (a : S) : N.1 a.1 ∉ U := by
    intro hn
    have he := (hMN a.1 a.2.1 (N.1 a.1) hn).mpr rfl
    exact a.2.2 (he.symm ▸ hn)
  let f : U ⊕ S → α := Sum.elim (fun a => a.1) (fun a => M.1 a.1)
  let g : U ⊕ S → α := Sum.elim (fun a => a.1) (fun a => N.1 a.1)
  have hf : Function.Injective f := by
    intro x y h
    cases x with
    | inl a =>
      cases y with
      | inl b => exact congrArg Sum.inl (Subtype.ext h)
      | inr b =>
        change a.1 = M.1 b.1 at h
        exact False.elim (b.2.2 (h ▸ a.2))
    | inr a =>
      cases y with
      | inl b =>
        change M.1 a.1 = b.1 at h
        exact False.elim (a.2.2 (h.symm ▸ b.2))
      | inr b => exact congrArg Sum.inr (Subtype.ext (M.1.injective h))
  have hg : Function.Injective g := by
    intro x y h
    cases x with
    | inl a =>
      cases y with
      | inl b => exact congrArg Sum.inl (Subtype.ext h)
      | inr b =>
        change a.1 = N.1 b.1 at h
        exact False.elim (hnout b (h ▸ a.2))
    | inr a =>
      cases y with
      | inl b =>
        change N.1 a.1 = b.1 at h
        exact False.elim (hnout a (h.symm ▸ b.2))
      | inr b => exact congrArg Sum.inr (Subtype.ext (N.1.injective h))
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  have hfix (a : α) (ha : a ∈ U) : p a = a := hp (Sum.inl ⟨a, ha⟩)
  have hpart (a : α) (ha : a ∈ U) : p (M.1 a) = N.1 a := by
    by_cases hm : M.1 a ∈ U
    · rw [hfix _ hm]
      exact ((hMN a ha (M.1 a) hm).mp rfl).symm
    · exact hp (Sum.inr ⟨a, ha, hm⟩)
  refine ⟨p, hfix, ?_⟩
  intro a ha
  have hi : p⁻¹ a = a := by
    calc
      p⁻¹ a = p⁻¹ (p a) := congrArg (fun b => p⁻¹ b) (hfix a ha).symm
      _ = a := by simp
  simp only [relabel_apply, hi, hpart a ha]

lemma mem_closure [DecidableEq α] (M : Pairing α) (U : Finset α) (a : α) :
    a ∈ closure M U ↔ a ∈ U ∨ M.1 a ∈ U := by
  simp only [closure, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (h | ⟨b, hb, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (by simpa using hb)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨M.1 a, h, M.partner_partner a⟩

lemma stable_closure [DecidableEq α] (M : Pairing α) (U : Finset α) (a : α) :
    M.1 a ∈ closure M U ↔ a ∈ closure M U := by
  simp only [mem_closure, partner_partner, or_comm]

lemma agree_on_closure [DecidableEq α] (U : Finset α) (M N : Pairing α)
    (h : ∀ a ∈ U, M.1 a = N.1 a) :
    ∀ a ∈ closure N U, M.1 a = N.1 a := by
  intro a ha
  rcases (mem_closure N U a).mp ha with ha | ha
  · exact h a ha
  · apply (M.partner_eq_iff a (N.1 a)).mpr
    rw [h _ ha, partner_partner]

lemma align_remaining [Fintype α] [DecidableEq α]
    (U : Finset α) (M N : Pairing α)
    (hMN : ∀ a ∈ U, M.1 a = N.1 a) :
    ∃ p : Equiv.Perm α, (∀ a ∈ U, p a = a) ∧ relabel p M = N := by
  classical
  let S := (closure N U)ᶜ
  have hagree := agree_on_closure U M N hMN
  have hcM : ∀ a ∈ closure N U, M.1 a ∈ closure N U := by
    intro a ha
    rw [hagree a ha]
    exact (stable_closure N U a).mpr ha
  have hcMi (a : α) : M.1 a ∈ closure N U ↔ a ∈ closure N U := by
    constructor
    · intro ha
      simpa using hcM (M.1 a) ha
    · exact hcM a
  have hM (a : α) : M.1 a ∈ S ↔ a ∈ S := by
    simp only [S, Finset.mem_compl, hcMi]
  have hN (a : α) : N.1 a ∈ S ↔ a ∈ S := by
    simp only [S, Finset.mem_compl, stable_closure]
  obtain ⟨q, hq⟩ := exists_relabel (restrict M S hM) (restrict N S hN)
  let p := q.extendDomain (Equiv.refl S)
  have hpin (a : α) (ha : a ∈ S) : p a = (q ⟨a, ha⟩).1 := by
    simpa [p] using Equiv.Perm.extendDomain_apply_subtype q (Equiv.refl S) ha
  have hpout (a : α) (ha : a ∉ S) : p a = a := by
    exact Equiv.Perm.extendDomain_apply_not_subtype q (Equiv.refl S) ha
  have hinter (a : α) : p (M.1 a) = N.1 (p a) := by
    by_cases ha : a ∈ S
    · have hh := congrArg (fun P : Pairing S => (P.1 (q ⟨a, ha⟩)).1) hq
      rw [hpin _ ((hM a).mpr ha), hpin a ha]
      simpa [restrict] using hh
    · have hma : M.1 a ∉ S := by simpa only [hM] using ha
      rw [hpout _ hma, hpout _ ha]
      exact hagree a (by simpa only [S, Finset.mem_compl, not_not] using ha)
  refine ⟨p, ?_, ?_⟩
  · intro a ha
    apply hpout
    simp only [S, Finset.mem_compl, not_not]
    exact (mem_closure N U a).mpr (Or.inl ha)
  · ext a
    obtain ⟨b, rfl⟩ := p.surjective a
    simpa using hinter b

lemma exists_relabel_fixing [Fintype α] [DecidableEq α]
    (U : Finset α) (M N : Pairing α) (hMN : SameInternal U M N) :
    ∃ p : Equiv.Perm α, (∀ a ∈ U, p a = a) ∧ relabel p M = N := by
  obtain ⟨p, hp, hpM⟩ := align_partners U M N hMN
  obtain ⟨q, hq, hqM⟩ := align_remaining U (relabel p M) N hpM
  refine ⟨q * p, ?_, ?_⟩
  · intro a ha
    simp only [Equiv.Perm.mul_apply, hp a ha, hq a ha]
  · rw [relabel_mul, hqM]

lemma extend_swap [DecidableEq α] (S : Finset α) (x y : S) :
    (Equiv.swap x y).extendDomain (Equiv.refl S) = Equiv.swap x.1 y.1 := by
  ext a
  by_cases ha : a ∈ S
  · rw [Equiv.Perm.extendDomain_apply_subtype _ _ ha]
    by_cases hx : a = x.1 <;> by_cases hy : a = y.1 <;>
      simp [Equiv.swap_apply_def, Subtype.ext_iff, hx, hy]
  · rw [Equiv.Perm.extendDomain_apply_not_subtype _ _ ha]
    have hx : a ≠ x.1 := by rintro rfl; exact ha x.2
    have hy : a ≠ y.1 := by rintro rfl; exact ha y.2
    simp [Equiv.swap_apply_def, hx, hy]

lemma invariant_of_swap_invariant [Fintype α] [DecidableEq α]
    (U : Finset α) (f : Pairing α → ℝ)
    (hf : ∀ a ∉ U, ∀ b ∉ U, a ≠ b → act (Equiv.swap a b) f = f)
    (p : Equiv.Perm α) (hp : ∀ a ∈ U, p a = a) : act p f = f := by
  classical
  let S := Uᶜ
  have hU (a : α) : p a ∈ U ↔ a ∈ U := by
    constructor
    · intro h
      have he : p a = a := p.injective (hp (p a) h)
      simpa [he] using h
    · intro h; simpa [hp a h] using h
  have hS (a : α) : p a ∈ S ↔ a ∈ S := by simp only [S, Finset.mem_compl, hU]
  have hind (q : Equiv.Perm S) : act (q.extendDomain (Equiv.refl S)) f = f := by
    induction q using Equiv.Perm.swap_induction_on with
    | one => simp
    | swap_mul q x y hxy ih =>
      rw [← Equiv.Perm.extendDomain_mul, act_mul, ih, extend_swap]
      apply hf x.1 (by simpa only [S, Finset.mem_compl] using x.2)
        y.1 (by simpa only [S, Finset.mem_compl] using y.2)
      exact fun h => hxy (Subtype.ext h)
  have he : (p.subtypePerm hS).extendDomain (Equiv.refl S) = p := by
    ext a
    by_cases ha : a ∈ S
    · rw [Equiv.Perm.extendDomain_apply_subtype _ _ ha]
      rfl
    · rw [Equiv.Perm.extendDomain_apply_not_subtype _ _ ha]
      exact (hp a (by simpa only [S, Finset.mem_compl, not_not] using ha)).symm
  rw [← he]
  exact hind _

lemma sameInternal_value_of_invariant [Fintype α] [DecidableEq α]
    (U : Finset α) (f : Pairing α → ℝ)
    (hf : ∀ a ∉ U, ∀ b ∉ U, a ≠ b → act (Equiv.swap a b) f = f)
    (M N : Pairing α) (hMN : SameInternal U M N) : f M = f N := by
  obtain ⟨p, hp, hpM⟩ := exists_relabel_fixing U M N hMN
  have he := congrFun (invariant_of_swap_invariant U f hf p hp) N
  rw [act_apply, ← hpM, ← relabel_mul, inv_mul_cancel, relabel_one] at he
  simpa only [hpM] using he

lemma internalPattern_eq_iff [DecidableEq α] (U : Finset α) (M N : Pairing α) :
    internalPattern U M = internalPattern U N ↔ SameInternal U M N := by
  constructor
  · intro h a ha b hb
    have he := Finset.ext_iff.mp h (a,b)
    simpa [internalPattern, ha, hb] using he
  · intro h
    ext ⟨a,b⟩
    simp only [internalPattern, Finset.mem_filter, Finset.mem_product]
    by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;> simp_all [SameInternal]

lemma internal_indicator_mem_lowDegree [Fintype α] [DecidableEq α]
    (U : Finset α) (M : Pairing α) :
    (fun N => if internalPattern U N = internalPattern U M then (1 : ℝ) else 0)
      ∈ lowDegree edgeCoord (U.card * U.card) := by
  classical
  have h := boolean_pattern_mem_lowDegree edgeCoord (U ×ˢ U) (internalPattern U M)
  rw [Finset.card_product] at h
  convert h using 1
  ext N
  rw [Finset.prod_apply]
  have hf (e : α × α) (he : e ∈ U ×ˢ U) :
      (if e ∈ internalPattern U M then edgeCoord e else 1 - edgeCoord e) N =
        (if (N.1 e.1 = e.2 ↔ M.1 e.1 = e.2) then (1 : ℝ) else 0) := by
    by_cases hm : M.1 e.1 = e.2 <;> by_cases hn : N.1 e.1 = e.2 <;>
      simp [internalPattern, he, hm, hn, edgeCoord]
  rw [Finset.prod_congr rfl hf, Finset.prod_boole]
  congr 1
  rw [internalPattern_eq_iff]
  simp only [SameInternal, Finset.mem_product, Prod.forall]
  aesop

lemma mem_lowDegree_of_swap_invariant [Fintype α] [DecidableEq α]
    (U : Finset α) (f : Pairing α → ℝ)
    (hf : ∀ a ∉ U, ∀ b ∉ U, a ≠ b → act (Equiv.swap a b) f = f) :
    f ∈ lowDegree edgeCoord (U.card * U.card) := by
  apply mem_of_fiber_indicators (internalPattern U) f
  · intro M N hMN
    exact sameInternal_value_of_invariant U f hf M N
      ((internalPattern_eq_iff U M N).mp hMN)
  · exact internal_indicator_mem_lowDegree U

lemma exists_perm_fixing_pair [Fintype α] [DecidableEq α]
    (U : Finset α) {a b c d : α} (ha : a ∉ U) (hb : b ∉ U)
    (hc : c ∉ U) (hd : d ∉ U) (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ p : Equiv.Perm α, (∀ u ∈ U, p u = u) ∧ p a = c ∧ p b = d := by
  let f : U ⊕ Bool → α := Sum.elim Subtype.val (fun i => cond i b a)
  let g : U ⊕ Bool → α := Sum.elim Subtype.val (fun i => cond i d c)
  have hi {x y : α} (hx : x ∉ U) (hy : y ∉ U) (hxy : x ≠ y) :
      Function.Injective (Sum.elim (Subtype.val : U → α) (fun i : Bool => cond i y x)) := by
    rw [Sum.elim_injective]
    refine ⟨Subtype.val_injective, ?_, ?_⟩
    · intro i j h
      cases i <;> cases j <;> simp_all
    · intro u i
      cases i <;> simp only [Bool.cond_false, Bool.cond_true]
      · intro h; exact hx (h ▸ u.2)
      · intro h; exact hy (h ▸ u.2)
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair f g (hi ha hb hab) (hi hc hd hcd)
  exact ⟨p, fun u hu => hp (Sum.inl ⟨u, hu⟩), hp (Sum.inr false), hp (Sum.inr true)⟩

lemma act_swap_involution [DecidableEq α] (a b : α) (f : Pairing α → ℝ) :
    act (Equiv.swap a b) (act (Equiv.swap a b) f) = f := by
  rw [← act_mul, Equiv.swap_mul_self, act_one]

lemma act_swap_conj [DecidableEq α] (p : Equiv.Perm α) (a b : α)
    (f : Pairing α → ℝ) :
    act (Equiv.swap (p a) (p b)) (act p f) = act p (act (Equiv.swap a b) f) := by
  rw [← act_mul, ← act_mul, Equiv.mul_swap_eq_swap_mul]

lemma act_commute_of_swap_fixed [DecidableEq α] (p : Equiv.Perm α) (a b : α)
    (ha : p a = a) (hb : p b = b) (f : Pairing α → ℝ) :
    act (Equiv.swap a b) (act p f) = act p (act (Equiv.swap a b) f) := by
  simpa only [ha, hb] using act_swap_conj p a b f

end Pairing
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.RepresentationDimension ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe u_1

namespace MatchingSmoothing
section StandardPairs

variable {h : ℕ}

lemma card_firstVertices {t : ℕ} (ht : t ≤ h) :
    (firstVertices h t).card = 2 * t := by
  simp [firstVertices, Fin.card_filter_val_lt, min_eq_right ht, Nat.mul_comm]

lemma pairSwap_commute (i j : Fin h) : Commute (pairSwap i) (pairSwap j) := by
  by_cases hij : i = j
  · subst j; exact Commute.refl _
  · change Equiv.swap (i,false) (i,true) * Equiv.swap (j,false) (j,true) =
      Equiv.swap (j,false) (j,true) * Equiv.swap (i,false) (i,true)
    rw [Equiv.mul_swap_eq_swap_mul]
    simp [Equiv.swap_apply_def, Ne.symm hij]

lemma act_pairSwap_commute (i j : Fin h) :
    Commute (Pairing.act (pairSwap i)).toLinearMap (Pairing.act (pairSwap j)).toLinearMap := by
  apply LinearMap.ext
  intro f
  change Pairing.act (pairSwap i) (Pairing.act (pairSwap j) f) = _
  rw [← Pairing.act_mul, (pairSwap_commute i j).eq, Pairing.act_mul]
  rfl

lemma pairSwap_fixed_outside {i : Fin h} {a b : Vertices h}
    (ha : a.1 ≠ i) (hb : b.1 ≠ i) :
    Equiv.swap a b (i,false) = (i,false) ∧ Equiv.swap a b (i,true) = (i,true) := by
  simp [Equiv.swap_apply_def, Prod.ext_iff, Ne.symm ha, Ne.symm hb]

lemma eigen_weighted_projection {V : Type u_1} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (hinv : ∀ v, A (A v) = v)
    (c : ℝ) (hc : c = 1 ∨ c = -1) (v : V) :
    A (v + c • A v) = c • (v + c • A v) := by
  rcases hc with rfl | rfl
  · simp [hinv, add_comm]
  · simp [hinv, add_comm]

lemma next_prescribed_sign (W : Submodule ℝ (Pairing (Vertices h) → ℝ))
    (hW : ∀ p f, f ∈ W → Pairing.act p f ∈ W)
    {t : ℕ} (ht : t < h) (χ : Fin h → ℝ) (c : ℝ) (hc : c = 1 ∨ c = -1)
    (f : Pairing (Vertices h) → ℝ) (hf : f ∈ W)
    (heig : ∀ i : Fin h, i.val < t → Pairing.act (pairSwap i) f = χ i • f)
    (hex : ∃ a, a ∉ firstVertices h t ∧ ∃ b, b ∉ firstVertices h t ∧ a ≠ b ∧
      f + c • Pairing.act (Equiv.swap a b) f ≠ 0) :
    ∃ g ∈ W, g ≠ 0 ∧ Pairing.act (pairSwap ⟨t, ht⟩) g = c • g ∧
      ∀ i : Fin h, i.val < t → Pairing.act (pairSwap i) g = χ i • g := by
  obtain ⟨a, ha, b, hb, hab, h0⟩ := hex
  let i : Fin h := ⟨t, ht⟩
  obtain ⟨p, hp, hpa, hpb⟩ := Pairing.exists_perm_fixing_pair (firstVertices h t)
    ha hb (c := (i,false)) (d := (i,true)) (by simp [i]) (by simp [i]) hab (by simp)
  let v := f + c • Pairing.act (Equiv.swap a b) f
  have hv : v ∈ W := W.add_mem hf (W.smul_mem c (hW _ _ hf))
  refine ⟨Pairing.act p v, hW _ _ hv, ?_, ?_, ?_⟩
  · intro hz
    apply h0
    change v = 0
    exact (Pairing.act p).injective (hz.trans (map_zero _).symm)
  · change Pairing.act (Equiv.swap (i,false) (i,true)) (Pairing.act p v) = _
    rw [← hpa, ← hpb, Pairing.act_swap_conj]
    have hvsign := eigen_weighted_projection (Pairing.act (Equiv.swap a b)).toLinearMap
      (Pairing.act_swap_involution a b) c hc f
    change Pairing.act (Equiv.swap a b) v = c • v at hvsign
    rw [hvsign, map_smul]
  · intro j hj
    have hpj (b : Bool) : p (j,b) = (j,b) := hp _ (by simpa using hj)
    change Pairing.act (Equiv.swap (j,false) (j,true)) (Pairing.act p v) = _
    rw [Pairing.act_commute_of_swap_fixed p _ _ (hpj false) (hpj true)]
    have haj : a.1 ≠ j := by
      intro he
      apply ha
      simpa only [mem_firstVertices, he] using hj
    have hbj : b.1 ≠ j := by
      intro he
      apply hb
      simpa only [mem_firstVertices, he] using hj
    obtain ⟨hfix₁, hfix₂⟩ := pairSwap_fixed_outside haj hbj
    have hpast : Pairing.act (pairSwap j) v = χ j • v := by
      change Pairing.act (Equiv.swap (j,false) (j,true))
        (f + c • Pairing.act (Equiv.swap a b) f) = _
      rw [map_add, map_smul, Pairing.act_commute_of_swap_fixed _ _ _ hfix₁ hfix₂]
      change Pairing.act (pairSwap j) f +
        c • Pairing.act (Equiv.swap a b) (Pairing.act (pairSwap j) f) = _
      rw [heig j hj, map_smul]
      change χ j • f + c • (χ j • Pairing.act (Equiv.swap a b) f) =
        χ j • (f + c • Pairing.act (Equiv.swap a b) f)
      rw [smul_add, smul_comm c (χ j)]
    change Pairing.act p (Pairing.act (pairSwap j) v) = _
    rw [hpast, map_smul]

lemma exists_negative_projection {α : Type u_1} [Fintype α] [DecidableEq α]
    (U : Finset α) (f : Pairing α → ℝ)
    (hf : f ∉ lowDegree Pairing.edgeCoord (U.card * U.card)) :
    ∃ a, a ∉ U ∧ ∃ b, b ∉ U ∧ a ≠ b ∧ f + (-1 : ℝ) • Pairing.act (Equiv.swap a b) f ≠ 0 := by
  by_contra! hall
  apply hf
  apply Pairing.mem_lowDegree_of_swap_invariant U f
  intro a ha b hb hab
  have he := hall a ha b hb hab
  have hz : f - Pairing.act (Equiv.swap a b) f = 0 := by
    simpa only [neg_smul, one_smul, sub_eq_add_neg] using he
  exact (sub_eq_zero.mp hz).symm

lemma exists_positive_projection {α : Type u_1} [Fintype α] [DecidableEq α]
    (U : Finset α) (hU : 2 * U.card < Fintype.card α)
    (f : Pairing α → ℝ) (hf : f ≠ 0) :
    ∃ a, a ∉ U ∧ ∃ b, b ∉ U ∧ a ≠ b ∧ f + (1 : ℝ) • Pairing.act (Equiv.swap a b) f ≠ 0 := by
  by_contra! hall
  apply hf
  apply Pairing.no_sign_on_complement U hU f
  intro a ha b hb hab
  have he := hall a ha b hb hab
  exact eq_neg_of_add_eq_zero_left (by simpa only [one_smul, add_comm] using he)

lemma prescribed_sign_vector (k : ℕ) (hk : 4 * k < h)
    (W : Submodule ℝ (Pairing (Vertices h) → ℝ))
    (hW : ∀ p f, f ∈ W → Pairing.act p f ∈ W)
    (hdis : Disjoint W (lowDegree Pairing.edgeCoord ((4 * k) * (4 * k))))
    (hne : ∃ f ∈ W, f ≠ 0) :
    ∃ f ∈ W, f ≠ 0 ∧ ∀ i : Fin h, i.val < 2 * k →
      Pairing.act (pairSwap i) f = (if i.val < k then (-1 : ℝ) else 1) • f := by
  let χ (i : Fin h) : ℝ := if i.val < k then -1 else 1
  have hind : ∀ t : ℕ, t ≤ 2 * k → ∃ f ∈ W, f ≠ 0 ∧
      ∀ i : Fin h, i.val < t → Pairing.act (pairSwap i) f = χ i • f := by
    intro t
    induction t with
    | zero =>
      intro _
      obtain ⟨f, hf, hf0⟩ := hne
      exact ⟨f, hf, hf0, by simp⟩
    | succ t ih =>
      intro ht
      obtain ⟨f, hf, hf0, he⟩ := ih (by omega)
      have hth : t < h := by omega
      let c : ℝ := if t < k then -1 else 1
      have hc : c = 1 ∨ c = -1 := by dsimp [c]; split_ifs <;> simp
      have hex : ∃ a, a ∉ firstVertices h t ∧ ∃ b, b ∉ firstVertices h t ∧ a ≠ b ∧
          f + c • Pairing.act (Equiv.swap a b) f ≠ 0 := by
        by_cases htk : t < k
        · dsimp [c]; rw [ite_eq_left htk]
          apply exists_negative_projection
          intro hlow
          have hd : (firstVertices h t).card * (firstVertices h t).card ≤ (4*k) * (4*k) := by
            rw [card_firstVertices hth.le]
            apply Nat.mul_self_le_mul_self
            omega
          exact hf0 ((Submodule.disjoint_def.mp hdis) f hf (lowDegree_mono _ hd hlow))
        · dsimp [c]; rw [ite_eq_right htk]
          apply exists_positive_projection _ _ f hf0
          rw [card_firstVertices hth.le]
          simp only [Vertices, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
          omega
      obtain ⟨g, hg, hg0, hnew, hold⟩ := next_prescribed_sign W hW hth χ c hc f hf he hex
      refine ⟨g, hg, hg0, ?_⟩
      intro i hi
      by_cases hit : i.val < t
      · exact hold i hit
      · have hie : i = ⟨t, hth⟩ := Fin.ext (by change i.val = t; omega)
        subst i
        exact hnew
  exact hind (2*k) le_rfl

lemma choose_le_choose_of_le_of_le_compl {n k w : ℕ}
    (hkw : k ≤ w) (hw : w ≤ n - k) : n.choose k ≤ n.choose w := by
  have hmon : ∀ a b : ℕ, a ≤ b → b ≤ n / 2 → n.choose a ≤ n.choose b := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => intro _; rfl
    | succ b hab ih =>
      intro hb
      exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))
  by_cases hhalf : w ≤ n / 2
  · exact hmon k w hkw hhalf
  · have hwn : w ≤ n := hw.trans (Nat.sub_le _ _)
    rw [← Nat.choose_symm hwn]
    apply hmon k (n-w) <;> omega

lemma invariant_high_degree_dimension (k : ℕ) (hk : 4 * k < h)
    (W : Submodule ℝ (Pairing (Vertices h) → ℝ))
    (hW : ∀ p f, f ∈ W → Pairing.act p f ∈ W)
    (hdis : Disjoint W (lowDegree Pairing.edgeCoord ((4 * k) * (4 * k))))
    (hne : ∃ f ∈ W, f ≠ 0) : h.choose k ≤ Module.finrank ℝ W := by
  classical
  obtain ⟨v, hv, hv0, he⟩ := prescribed_sign_vector k hk W hW hdis hne
  let A (i : Fin h) := (Pairing.act (pairSwap i)).toLinearMap
  let s₀ := Finset.univ.filter fun i : Fin h => i.val < 2*k
  obtain ⟨ψ, w, hw, hw0, hew, hp⟩ := simultaneous_sign_eigenvector_preserving A
    act_pairSwap_commute (fun i => Pairing.act_swap_involution (i,false) (i,true))
    W (fun i => hW (pairSwap i)) s₀ (fun i => if i.val < k then -1 else 1)
    v hv hv0 (by simpa [A, s₀] using he)
  have hpres (i : Fin h) (hi : i.val < 2*k) : ψ i = if i.val < k then -1 else 1 :=
    hp i (by simpa only [s₀, Finset.mem_filter, Finset.mem_univ, true_and] using hi)
  let s := Finset.univ.filter fun i => ψ i = -1
  have hlow : k ≤ s.card := by
    let e (i : Fin k) : s := ⟨⟨i.val, by omega⟩, by
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hpres _ (by dsimp; omega)]
      exact ite_eq_left i.isLt⟩
    have hinj : Function.Injective e := by
      intro i j hij
      exact Fin.ext (congrArg (fun x : s => x.1.val) hij)
    simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective e hinj
  have hhigh : k ≤ sᶜ.card := by
    let e (i : Fin k) : ↥(sᶜ) := ⟨⟨k+i.val, by omega⟩, by
      simp only [Finset.mem_compl, s, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hpres _ (by dsimp; omega), ite_eq_right (by dsimp; omega)]
      norm_num⟩
    have hinj : Function.Injective e := by
      intro i j hij
      have heq := congrArg (fun x : ↥(sᶜ) => x.1.val) hij
      apply Fin.ext
      dsimp [e] at heq
      omega
    simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective e hinj
  have hsc : s.card ≤ h := Finset.card_le_univ s |>.trans_eq (Fintype.card_fin h)
  rw [Finset.card_compl, Fintype.card_fin] at hhigh
  have hchoose := choose_le_choose_of_le_of_le_compl hlow (by omega : s.card ≤ h-k)
  apply hchoose.trans
  let P (p : Equiv.Perm (Fin h)) := Pairing.act (Equiv.prodCongr p (Equiv.refl Bool))
  have hconj (p : Equiv.Perm (Fin h)) (i : Fin h) (f : Pairing (Vertices h) → ℝ) :
      A (p i) (P p f) = P p (A i f) :=
    Pairing.act_swap_conj (Equiv.prodCongr p (Equiv.refl Bool)) (i,false) (i,true) f
  have hsigne (i : Fin h) : A i w = (if i ∈ s then (-1 : ℝ) else 1) • w := by
    have hi := hew i
    rw [hi.2]
    congr 1
    by_cases his : ψ i = -1
    · simp [s, his]
    · have hie : ψ i = 1 := hi.1.resolve_right his
      simp [s, hie]
  simpa only [Fintype.card_fin] using
    binomial_le_finrank_of_eigenvector_mem A act_pairSwap_commute P hconj W
      (fun p => hW _) s w hw hw0 hsigne

end StandardPairs
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.ColoringCounts ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace MatchingSmoothing

variable {α : Type u_1} {β : Type u_2} [Fintype α] [DecidableEq β]

lemma sum_histogram [Fintype β] (f : α → β) : ∑ b, histogram f b = Fintype.card α := by
  classical
  simp only [histogram]
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv f)

lemma permOfHistogram_spec {f g : α → β} (h : histogram f = histogram g)
    (a : α) : g (permOfHistogram h a) = f a := by
  exact (fiberEquivOfHistogram h (f a) ⟨a, rfl⟩).property

lemma card_colorings_mul_factorials [Fintype β] (f : α → β) :
    Fintype.card (Colorings α β (histogram f)) *
      (∏ b, (histogram f b).factorial) = (Fintype.card α).factorial := by
  classical
  let F : Equiv.Perm α → Colorings α β (histogram f) :=
    fun σ => ⟨f ∘ σ, histogram_comp_perm f σ⟩
  have hf (g : Colorings α β (histogram f)) :
      Fintype.card {σ // F σ = g} = ∏ b, (histogram f b).factorial := by
    let e₁ : {σ // F σ = g} ≃ {σ : Equiv.Perm α // f ∘ σ = g.1} :=
      Equiv.subtypeEquivRight (fun σ => Subtype.ext_iff)
    rw [Fintype.card_congr e₁, Fintype.card_congr (fiberPermEquiv f g.1),
      Fintype.card_pi]
    apply Finset.prod_congr rfl
    intro b _
    rw [Fintype.card_equiv (fiberEquivOfHistogram g.2 b)]
    exact congrArg Nat.factorial (congrFun g.2 b)
  have he := Fintype.card_congr (Equiv.sigmaFiberEquiv F)
  rw [Fintype.card_sigma, Fintype.card_perm] at he
  simpa only [hf, Finset.sum_const, Finset.card_univ, smul_eq_mul] using he

lemma card_colorings_eq_multinomial [Fintype β] (f : α → β) :
    Fintype.card (Colorings α β (histogram f)) =
      Nat.multinomial Finset.univ (histogram f) := by
  have h := card_colorings_mul_factorials f
  rw [Nat.multinomial, sum_histogram f, ← h, Nat.mul_div_cancel]
  exact Finset.prod_pos (by intro b _; exact Nat.factorial_pos _)

lemma card_perm_color_fiber [DecidableEq α] [Fintype β] (f : α → β) (g : Colorings α β (histogram f)) :
    Fintype.card {σ : Equiv.Perm α // f ∘ σ = g.1} =
      ∏ b, (histogram f b).factorial := by
  classical
  rw [Fintype.card_congr (fiberPermEquiv f g.1), Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro b _
  rw [Fintype.card_equiv (fiberEquivOfHistogram g.2 b)]
  exact congrArg Nat.factorial (congrFun g.2 b)

lemma sum_perm_comp [DecidableEq α] [Fintype β] (f : α → β) (φ : (α → β) → ℝ) :
    ∑ σ : Equiv.Perm α, φ (f ∘ σ) =
      (∏ b, ((histogram f b).factorial : ℝ)) *
        ∑ g : Colorings α β (histogram f), φ g.1 := by
  classical
  let F : Equiv.Perm α → Colorings α β (histogram f) :=
    fun σ => ⟨f ∘ σ, histogram_comp_perm f σ⟩
  rw [← Fintype.sum_fiberwise F (fun σ => φ (f ∘ σ)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  have he : ∀ σ : {σ // F σ = g}, φ (f ∘ σ.1) = φ g.1 := by
    intro σ
    exact congrArg φ (congrArg Subtype.val σ.2)
  simp_rw [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  let e : {σ // F σ = g} ≃ {σ : Equiv.Perm α // f ∘ σ = g.1} :=
    Equiv.subtypeEquivRight (fun σ => Subtype.ext_iff)
  rw [Fintype.card_congr e, card_perm_color_fiber]
  simp

lemma mean_perm_comp [DecidableEq α] [Fintype β] (f : α → β) (φ : (α → β) → ℝ) :
    (Fintype.card (Colorings α β (histogram f)) : ℝ) *
      (∑ σ : Equiv.Perm α, φ (f ∘ σ)) =
    (Fintype.card (Equiv.Perm α) : ℝ) *
      ∑ g : Colorings α β (histogram f), φ g.1 := by
  rw [sum_perm_comp, ← mul_assoc]
  congr 1
  have h := card_colorings_mul_factorials f
  rw [Fintype.card_perm]
  exact_mod_cast h

variable {H : Type u_5} [Fintype H] [DecidableEq H]

omit [DecidableEq H] in
lemma card_colorings_double_ge_square [Fintype β] (s : β → ℕ) :
    Fintype.card (Colorings H β s) ^ 2 ≤
      Fintype.card (Colorings (H × Bool) β (fun b => 2 * s b)) := by
  classical
  let e : Colorings H β s × Colorings H β s →
      Colorings (H × Bool) β (fun b => 2 * s b) := fun kl =>
    ⟨spliceColoring kl.1.1 kl.2.1, by
      rw [histogram_spliceColoring, kl.1.2, kl.2.2]
      funext b; simp [two_mul]⟩
  have hi : Function.Injective e := by
    intro kl mn h
    apply Prod.ext
    · apply Subtype.ext
      funext i
      exact congrFun (congrArg Subtype.val h) (i, false)
    · apply Subtype.ext
      funext i
      exact congrFun (congrArg Subtype.val h) (i, true)
  simpa only [Fintype.card_prod, pow_two] using Fintype.card_le_of_injective e hi

lemma sum_indicator_card {X : Type u_6} [Fintype X] (p : X → Prop) [DecidablePred p] :
    (∑ x, if p x then (1 : ℝ) else 0) = (Fintype.card {x // p x} : ℝ) := by
  simp only [Fintype.card_subtype, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> norm_num

lemma sum_pairConstant (F : (H × Bool → β) → ℝ) [Fintype β] :
    (∑ f, if pairConstant f then F f else 0) = ∑ k : H → β, F (duplicateColoring k) := by
  classical
  rw [← Finset.sum_filter, ← Finset.sum_subtype_eq_sum_filter]
  simp only [Finset.subtype_univ]
  exact Fintype.sum_equiv pairConstantEquiv _ _ (by
    intro f
    congr 1
    exact (congrArg Subtype.val (pairConstantEquiv.symm_apply_apply f)).symm)

lemma pairConstant_perm_sum_bound [Fintype β] (k : H → β) :
    (Fintype.card (Colorings H β (histogram k)) : ℝ) *
      (∑ σ : Equiv.Perm (H × Bool),
        if pairConstant (duplicateColoring k ∘ σ) then (1 : ℝ) else 0) ≤
        Fintype.card (Equiv.Perm (H × Bool)) := by
  classical
  let A := Fintype.card (Colorings H β (histogram k))
  let B := Fintype.card (Colorings (H × Bool) β (fun b => 2 * histogram k b))
  let S := ∑ σ : Equiv.Perm (H × Bool),
    if pairConstant (duplicateColoring k ∘ σ) then (1 : ℝ) else 0
  have hA : (0 : ℝ) < A := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨⟨k, rfl⟩⟩ : 0 < A)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
  have hB : (A : ℝ) ^ 2 ≤ B := by exact_mod_cast card_colorings_double_ge_square (histogram k)
  have he := mean_perm_comp (duplicateColoring k)
    (fun g => if pairConstant g then (1 : ℝ) else 0)
  rw [histogram_duplicateColoring] at he
  conv_rhs at he =>
    arg 2
    rw [sum_indicator_card, Fintype.card_congr (constantColoringsEquiv (histogram k))]
  change (B : ℝ) * S = _ at he
  change (A : ℝ) * S ≤ _
  nlinarith [mul_le_mul_of_nonneg_right hB hS]

lemma sum_le_card_mul_of_fiber_bound {X : Type u_7} {J : Type u_8} [Fintype X] [Fintype J]
    [DecidableEq J] (g : X → J) (a : X → ℝ) (P : ℝ) (hP : 0 ≤ P)
    (ha : ∀ x, (Fintype.card {y // g y = g x} : ℝ) * a x ≤ P) :
    ∑ x, a x ≤ (Fintype.card J : ℝ) * P := by
  rw [← Fintype.sum_fiberwise g a]
  calc
    _ ≤ ∑ _j : J, P := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hn : Nonempty {y // g y = j}
      · have hc : (0 : ℝ) < Fintype.card {y // g y = j} := by
          exact_mod_cast Fintype.card_pos_iff.mpr hn
        apply (mul_le_mul_iff_right₀ hc).mp
        rw [Finset.mul_sum]
        calc
          _ ≤ ∑ _y : {y // g y = j}, P := by
            apply Finset.sum_le_sum
            intro y _
            simpa only [y.2] using ha y.1
          _ = _ := by simp
      · have : IsEmpty {y // g y = j} := ⟨fun y => hn ⟨y⟩⟩
        simpa using hP
    _ = _ := by simp

omit [DecidableEq H] in
lemma boundedHistogram_eq_iff (f g : H → β) :
    boundedHistogram f = boundedHistogram g ↔ histogram f = histogram g := by
  constructor
  · intro h; funext b; exact congrArg Fin.val (congrFun h b)
  · intro h; funext b; apply Fin.ext; exact congrFun h b

lemma common_pairColorings_moment [Fintype β] :
    (∑ σ : Equiv.Perm (H × Bool),
      (Fintype.card {f : H × Bool → β // pairConstant f ∧ pairConstant (f ∘ σ)} : ℝ)) ≤
    (Fintype.card (Equiv.Perm (H × Bool)) : ℝ) *
      (Fintype.card H + 1 : ℝ) ^ Fintype.card β := by
  classical
  conv_lhs =>
    arg 2
    ext σ
    rw [← sum_indicator_card]
  rw [Finset.sum_comm]
  have he (f : H × Bool → β) :
      ∑ σ : Equiv.Perm (H × Bool),
        (if pairConstant f ∧ pairConstant (f ∘ σ) then (1 : ℝ) else 0) =
      if pairConstant f then ∑ σ : Equiv.Perm (H × Bool),
        (if pairConstant (f ∘ σ) then (1 : ℝ) else 0) else 0 := by
    split_ifs with hf <;> simp [hf]
  simp_rw [he]
  rw [sum_pairConstant]
  have hb := sum_le_card_mul_of_fiber_bound (boundedHistogram (H := H) (β := β))
    (fun k => ∑ σ : Equiv.Perm (H × Bool),
      if pairConstant (duplicateColoring k ∘ σ) then (1 : ℝ) else 0)
    (Fintype.card (Equiv.Perm (H × Bool)) : ℝ) (by positivity) (by
      intro k
      let e : {l : H → β // boundedHistogram l = boundedHistogram k} ≃
          Colorings H β (histogram k) :=
        Equiv.subtypeEquivRight (fun l => boundedHistogram_eq_iff l k)
      rw [Fintype.card_congr e]
      exact pairConstant_perm_sum_bound k)
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_add,
    Nat.cast_one, mul_comm] using hb

end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.TransitionMatrices ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement).
private abbrev Finset.prod_le_one₀ := @Finset.prod_le_one

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing
open Matrix

variable {V : Type u_1} {C : Type u_2} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C]

omit [DecidableEq C] in
lemma tensorKernel_mul (U W : Matrix C C ℝ) :
    tensorKernel (V := V) (U * W) = tensorKernel (V := V) U * tensorKernel W := by
  classical
  ext f g
  simp only [tensorKernel, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro h _
  exact Finset.prod_mul_distrib

omit [Fintype C] [DecidableEq V] [DecidableEq C] in
lemma tensorKernel_transpose (U : Matrix C C ℝ) :
    tensorKernel (V := V) U.transpose = (tensorKernel U).transpose := rfl

omit [Fintype C] [DecidableEq V] in
lemma tensorKernel_one :
    tensorKernel (V := V) (1 : Matrix C C ℝ) = 1 := by
  classical
  ext f g
  by_cases h : f = g
  · subst g; simp [tensorKernel]
  · have he : ∃ v, f v ≠ g v := Function.ne_iff.mp h
    obtain ⟨v, hv⟩ := he
    simp only [tensorKernel, Matrix.one_apply, ite_eq_right h]
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    simp [hv]

lemma tensorKernel_orthogonal (U : Matrix C C ℝ)
    (hU : U.transpose * U = 1) :
    (tensorKernel (V := V) U).transpose * tensorKernel (V := V) U = 1 := by
  rw [← tensorKernel_transpose, ← tensorKernel_mul, hU, tensorKernel_one]

lemma tensorKernel_overlap (U : Matrix C C ℝ)
    (hU : U.transpose * U = 1) (x y : (V → C) → ℝ) :
    (tensorKernel U *ᵥ x) ⬝ᵥ (tensorKernel U *ᵥ y) = x ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, tensorKernel_orthogonal U hU,
    Matrix.vecMul_one]

omit [Fintype C] [DecidableEq V] [DecidableEq C] in
lemma tensorKernel_relabel (U : Matrix C C ℝ) (σ : Equiv.Perm V) (f g : V → C) :
    tensorKernel U (f ∘ σ) (g ∘ σ) = tensorKernel U f g := by
  exact Equiv.prod_comp σ (fun v => U (f v) (g v))

omit [DecidableEq C] in
lemma tensorKernel_mulVec_relabel (U : Matrix C C ℝ) (σ : Equiv.Perm V)
    (x : (V → C) → ℝ) (f : V → C) :
    (tensorKernel U *ᵥ (fun g => x (g ∘ σ))) f =
      (tensorKernel U *ᵥ x) (f ∘ σ) := by
  classical
  let e : (V → C) ≃ (V → C) := Equiv.arrowCongr σ (Equiv.refl C)
  change ∑ g, tensorKernel U f g * x (g ∘ σ) =
    ∑ g, tensorKernel U (f ∘ σ) g * x g
  refine Fintype.sum_equiv e.symm _ _ ?_
  intro g
  have he : e.symm g = g ∘ σ := rfl
  rw [he, tensorKernel_relabel]

variable {H : Type u_3} [Fintype H] [DecidableEq H]

lemma tensorKernel_mulVec_pairDiagonal (U : Matrix C C ℝ) (d : C → ℝ)
    (f : H × Bool → C) :
    (tensorKernel U *ᵥ pairDiagonal d) f =
      pairWeight (U * diagonal d * U.transpose) f := by
  classical
  change ∑ g, (∏ v, U (f v) (g v)) *
    (if pairConstant g then ∏ i, d (g (i, false)) else 0) = _
  simp only [mul_ite, mul_zero]
  rw [sum_pairConstant]
  simp only [duplicateColoring, Fintype.prod_prod_type, Fintype.prod_bool]
  have hm (a b : C) : (U * diagonal d * U.transpose) a b =
      ∑ c, U a c * d c * U b c := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  simp only [pairWeight, hm]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  ring

lemma pairWeight_overlap (U : Matrix C C ℝ) (d : C → ℝ)
    (hU : U.transpose * U = 1) (σ : Equiv.Perm (H × Bool)) :
    (∑ f : H × Bool → C, pairWeight (U * diagonal d * U.transpose) f *
      pairWeight (U * diagonal d * U.transpose) (f ∘ σ)) =
    ∑ f : H × Bool → C, pairDiagonal d f * pairDiagonal d (f ∘ σ) := by
  simp_rw [← tensorKernel_mulVec_pairDiagonal,
    ← tensorKernel_mulVec_relabel U σ (pairDiagonal d)]
  exact tensorKernel_overlap U hU _ _

omit [Fintype C] [DecidableEq H] in
lemma pairDiagonal_abs_le (d : C → ℝ) (hd : ∀ c, |d c| ≤ 1) (f : H × Bool → C) :
    |pairDiagonal d f| ≤ 1 := by
  classical
  unfold pairDiagonal
  split_ifs
  · rw [Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun _ _ => hd _)
  · simp

lemma pairWeight_overlap_le (U : Matrix C C ℝ) (d : C → ℝ)
    (hU : U.transpose * U = 1) (hd : ∀ c, |d c| ≤ 1)
    (σ : Equiv.Perm (H × Bool)) :
    (∑ f : H × Bool → C, pairWeight (U * diagonal d * U.transpose) f *
      pairWeight (U * diagonal d * U.transpose) (f ∘ σ)) ≤
    (Fintype.card {f : H × Bool → C // pairConstant f ∧ pairConstant (f ∘ σ)} : ℝ) := by
  classical
  rw [pairWeight_overlap U d hU σ]
  have he : (Fintype.card {f : H × Bool → C // pairConstant f ∧ pairConstant (f ∘ σ)} : ℝ) =
      ∑ f : H × Bool → C, if pairConstant f ∧ pairConstant (f ∘ σ) then (1 : ℝ) else 0 := by
    simp only [Fintype.card_subtype, Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro f _
    split_ifs <;> norm_num
  rw [he]
  apply Finset.sum_le_sum
  intro f _
  by_cases hf : pairConstant f ∧ pairConstant (f ∘ σ)
  · rw [ite_eq_left hf]
    exact (le_abs_self _).trans (by
      rw [abs_mul]
      exact (mul_le_mul (pairDiagonal_abs_le d hd f)
        (pairDiagonal_abs_le d hd (f ∘ σ)) (abs_nonneg _) zero_le_one).trans_eq (mul_one _))
  · rw [ite_eq_right hf]
    rcases not_and_or.mp hf with hf | hf <;> simp [pairDiagonal, hf]

end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.TensorBounds ----
namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing
open Matrix

variable {C : Type u_1} [Fintype C] [DecidableEq C]

lemma abs_eigenvalue_le_one_stochastic (W : Matrix C C ℝ)
    (hn : ∀ i j, 0 ≤ W i j) (hs : ∀ i, ∑ j, W i j = 1)
    (c : ℝ) (hc : Module.End.HasEigenvalue (Matrix.toLin' W) c) : |c| ≤ 1 := by
  obtain ⟨i, hi⟩ := eigenvalue_mem_ball hc
  rw [mem_closedBall_iff_norm] at hi
  simp only [Real.norm_eq_abs, abs_of_nonneg (hn _ _)] at hi
  have he := Finset.sum_erase_add (Finset.univ : Finset C) (fun j => W i j)
    (Finset.mem_univ i)
  rw [hs] at he
  calc
    |c| = |(c - W i i) + W i i| := by congr 1; ring
    _ ≤ |c - W i i| + |W i i| := abs_add_le _ _
    _ ≤ 1 := by rw [abs_of_nonneg (hn _ _)]; linarith

lemma abs_eigenvalue_le_one_positive_fixed (A : Matrix C C ℝ)
    (hn : ∀ i j, 0 ≤ A i j) (v : C → ℝ) (hv : ∀ i, 0 < v i)
    (hf : A *ᵥ v = v) (c : ℝ)
    (hc : Module.End.HasEigenvalue (Matrix.toLin' A) c) : |c| ≤ 1 := by
  let W : Matrix C C ℝ := fun i j => A i j * v j / v i
  apply abs_eigenvalue_le_one_stochastic W
  · intro i j; exact div_nonneg (mul_nonneg (hn i j) (hv j).le) (hv i).le
  · intro i
    change ∑ j, A i j * v j / v i = 1
    rw [← Finset.sum_div]
    change (A *ᵥ v) i / v i = 1
    rw [hf, div_self (ne_of_gt (hv i))]
  · obtain ⟨x, hx, hnx⟩ := hc.exists_hasEigenvector
    let y : C → ℝ := fun i => x i / v i
    have hy : y ≠ 0 := by
      intro h
      apply hnx
      ext i
      have he := congrFun h i
      change x i / v i = 0 at he
      exact (div_eq_zero_iff.mp he).resolve_right (ne_of_gt (hv i))
    apply Module.End.hasEigenvalue_of_hasEigenvector
    refine ⟨?_, hy⟩
    rw [Module.End.mem_eigenspace_iff]
    ext i
    change ∑ j, (A i j * v j / v i) * (x j / v j) = c * (x i / v i)
    have hh (j : C) : A i j * v j / v i * (x j / v j) = A i j * x j / v i := by
      field_simp [ne_of_gt (hv j), ne_of_gt (hv i)]
    simp_rw [hh]
    rw [← Finset.sum_div]
    have hhx := congrFun (Module.End.mem_eigenspace_iff.mp hx) i
    change ∑ j, A i j * x j = c * x i at hhx
    rw [hhx]
    ring

lemma exists_orthogonal_diagonalization_bounded (A : Matrix C C ℝ)
    (hA : A.IsHermitian) (hn : ∀ i j, 0 ≤ A i j)
    (v : C → ℝ) (hv : ∀ i, 0 < v i) (hf : A *ᵥ v = v) :
    ∃ U : Matrix C C ℝ, ∃ d : C → ℝ,
      U.transpose * U = 1 ∧ (∀ i, |d i| ≤ 1) ∧ A = U * diagonal d * U.transpose := by
  refine ⟨hA.eigenvectorUnitary, hA.eigenvalues, ?_, ?_, ?_⟩
  · simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hA.eigenvectorUnitary.property.1
  · intro i
    apply abs_eigenvalue_le_one_positive_fixed A hn v hv hf
    apply Module.End.hasEigenvalue_of_hasEigenvector
    refine ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      exact hA.mulVec_eigenvectorBasis i
    · intro h
      have he : hA.eigenvectorBasis i = 0 := by
        exact PiLp.ext (fun j => congrFun h j)
      exact (hA.eigenvectorBasis.orthonormal.ne_zero i) he
  · simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hA.spectral_theorem

end MatchingSmoothing

namespace MatchingSmoothing
open Matrix
variable {H : Type u_2} {C : Type u_3} [Fintype H] [Fintype C] [DecidableEq H] [DecidableEq C]

lemma commonColorings_square (σ : Equiv.Perm (H × Bool)) :
    (Fintype.card {f : H × Bool → C // pairConstant f ∧ pairConstant (f ∘ σ)}) ^ 2 =
    Fintype.card {f : H × Bool → C × C // pairConstant f ∧ pairConstant (f ∘ σ)} := by
  rw [pow_two, ← Fintype.card_prod]
  exact Fintype.card_congr (commonColoringsProdEquiv σ)

omit [Fintype C] [DecidableEq H] [DecidableEq C] in
lemma pairWeight_nonneg (A : Matrix C C ℝ) (hn : ∀ i j, 0 ≤ A i j)
    (f : H × Bool → C) : 0 ≤ pairWeight A f := by
  exact Finset.prod_nonneg (fun _ _ => hn _ _)

lemma pairWeight_overlap_square_moment (A : Matrix C C ℝ)
    (hA : A.IsHermitian) (hn : ∀ i j, 0 ≤ A i j)
    (v : C → ℝ) (hv : ∀ i, 0 < v i) (hf : A *ᵥ v = v) :
    (∑ σ : Equiv.Perm (H × Bool),
      (∑ f : H × Bool → C, pairWeight A f * pairWeight A (f ∘ σ)) ^ 2) ≤
    (Fintype.card (Equiv.Perm (H × Bool)) : ℝ) *
      (Fintype.card H + 1 : ℝ) ^ (Fintype.card C) ^ 2 := by
  obtain ⟨U, d, hU, hd, he⟩ := exists_orthogonal_diagonalization_bounded A hA hn v hv hf
  have hp (σ : Equiv.Perm (H × Bool)) :
      (∑ f : H × Bool → C, pairWeight A f * pairWeight A (f ∘ σ)) ^ 2 ≤
      (Fintype.card {f : H × Bool → C × C // pairConstant f ∧ pairConstant (f ∘ σ)} : ℝ) := by
    rw [← commonColorings_square, Nat.cast_pow]
    apply pow_le_pow_left₀
    · exact Finset.sum_nonneg (fun f _ => mul_nonneg (pairWeight_nonneg A hn f)
        (pairWeight_nonneg A hn (f ∘ σ)))
    · rw [he]
      exact pairWeight_overlap_le U d hU hd σ
  have h := (Finset.sum_le_sum (fun σ (_ : σ ∈ Finset.univ) => hp σ)).trans
    (common_pairColorings_moment (H := H) (β := C × C))
  simpa only [Fintype.card_prod, pow_two] using h

omit [Fintype C] [DecidableEq C] in
lemma normalizedPairMatrix_nonneg (γ : Matrix C C ℝ) (π : C → ℝ)
    (hn : ∀ i j, 0 ≤ γ i j) : ∀ i j, 0 ≤ normalizedPairMatrix γ π i j := by
  intro i j
  exact div_nonneg (hn i j) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

omit [Fintype C] [DecidableEq C] in
lemma normalizedPairMatrix_hermitian (γ : Matrix C C ℝ) (π : C → ℝ)
    (hs : γ.IsHermitian) : (normalizedPairMatrix γ π).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff] at hs ⊢
  intro i j
  simp only [star_trivial] at hs ⊢
  simp only [normalizedPairMatrix, hs j i, mul_comm]

omit [DecidableEq C] in
lemma normalizedPairMatrix_fixed (γ : Matrix C C ℝ) (π : C → ℝ)
    (hp : ∀ i, 0 < π i) (hs : ∀ i, ∑ j, γ i j = π i) :
    normalizedPairMatrix γ π *ᵥ (fun i => Real.sqrt (π i)) = fun i => Real.sqrt (π i) := by
  ext i
  have he (j : C) : γ i j / (Real.sqrt (π i) * Real.sqrt (π j)) * Real.sqrt (π j) =
      γ i j / Real.sqrt (π i) := by
    field_simp [ne_of_gt (Real.sqrt_pos.mpr (hp j)), ne_of_gt (Real.sqrt_pos.mpr (hp i))]
  change ∑ j, γ i j / (Real.sqrt (π i) * Real.sqrt (π j)) * Real.sqrt (π j) = _
  simp_rw [he]
  rw [← Finset.sum_div, hs]
  exact (div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr (hp i)))).mpr
    (Real.mul_self_sqrt (hp i).le).symm

end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.TypeProbabilities ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
private abbrev Finset.prod_le_prod₀ := @Finset.prod_le_prod

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace MatchingSmoothing

lemma pow_mul_factorial_le_mode (t j : ℕ) :
    t ^ j * t.factorial ≤ t ^ t * j.factorial := by
  rcases le_total j t with hj | ht
  · have he : t.factorial = j.factorial * t.descFactorial (t - j) := by
      simpa only [Nat.sub_sub_self hj] using
        (Nat.factorial_mul_descFactorial (Nat.sub_le t j)).symm
    calc
      t ^ j * t.factorial = t ^ j * (j.factorial * t.descFactorial (t - j)) := by rw [he]
      _ ≤ t ^ j * (j.factorial * t ^ (t - j)) := by
        gcongr; exact Nat.descFactorial_le_pow _ _
      _ = t ^ t * j.factorial := by
        rw [mul_comm j.factorial (t ^ (t - j)), ← mul_assoc, ← pow_add, Nat.add_sub_of_le hj]
  · have he : j.factorial = t.factorial * (t + 1).ascFactorial (j - t) := by
      simpa only [Nat.add_sub_of_le ht] using (Nat.factorial_mul_ascFactorial t (j - t)).symm
    have hp : t ^ (j - t) ≤ (t + 1).ascFactorial (j - t) :=
      (Nat.pow_le_pow_left (Nat.le_succ t) _).trans (Nat.pow_succ_le_ascFactorial _ _)
    calc
      t ^ j * t.factorial = t ^ t * (t.factorial * t ^ (j - t)) := by
        rw [mul_comm t.factorial (t ^ (j - t)), ← mul_assoc, ← pow_add, Nat.add_sub_of_le ht]
      _ ≤ t ^ t * (t.factorial * (t + 1).ascFactorial (j - t)) := by gcongr
      _ = t ^ t * j.factorial := by rw [he]

lemma poisson_mass_le_integer_mode (t j : ℕ) :
    (t : ℝ) ^ j / j.factorial ≤ (t : ℝ) ^ t / t.factorial := by
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < j.factorial)
    (by positivity : (0 : ℝ) < t.factorial)).mpr
  exact_mod_cast pow_mul_factorial_le_mode t j

lemma multinomial_term_eq {ι : Type u_1} (s : Finset ι) (k : ι → ℕ) (a : ι → ℝ) :
    (Nat.multinomial s k : ℝ) * ∏ i ∈ s, a i ^ k i =
      ((∑ i ∈ s, k i).factorial : ℝ) * ∏ i ∈ s, (a i ^ k i / (k i).factorial) := by
  rw [Finset.prod_div_distrib]
  have he : (∏ i ∈ s, ((k i).factorial : ℝ)) * Nat.multinomial s k =
      ((∑ i ∈ s, k i).factorial : ℝ) := by exact_mod_cast Nat.multinomial_spec s k
  rw [← he]
  have hn : ∏ i ∈ s, ((k i).factorial : ℝ) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (by intro i _; positivity)
  field_simp

lemma multinomial_term_le_mode {ι : Type u_2} (s : Finset ι) (t k : ι → ℕ)
    (hk : ∑ i ∈ s, k i = ∑ i ∈ s, t i) :
    (Nat.multinomial s k : ℝ) * ∏ i ∈ s, (t i : ℝ) ^ k i ≤
      (Nat.multinomial s t : ℝ) * ∏ i ∈ s, (t i : ℝ) ^ t i := by
  rw [multinomial_term_eq, multinomial_term_eq, hk]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.prod_le_prod₀
  · intro i _; positivity
  · intro i _; exact poisson_mass_le_integer_mode _ _

lemma card_piAntidiag_univ_le {ι : Type u_3} [Fintype ι] [DecidableEq ι] (n : ℕ) :
    (Finset.piAntidiag (Finset.univ : Finset ι) n).card ≤
      (n + 1) ^ Fintype.card ι := by
  classical
  let s := Finset.piAntidiag (Finset.univ : Finset ι) n
  have hn (k : s) (i : ι) : k.1 i ≤ n := by
    have he := (Finset.mem_piAntidiag.mp k.2).1
    rw [← he]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  let e : s → (ι → Fin (n + 1)) := fun k i => ⟨k.1 i, Nat.lt_succ_of_le (hn k i)⟩
  have hi : Function.Injective e := by
    intro k l h
    apply Subtype.ext
    funext i
    exact congrArg Fin.val (congrFun h i)
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] using
    Fintype.card_le_of_injective e hi

lemma multinomial_mode_lower {ι : Type u_4} [Fintype ι] [DecidableEq ι]
    (t : ι → ℕ) (n : ℕ) (ht : ∑ i, t i = n) :
    (n : ℝ) ^ n ≤ (n + 1 : ℝ) ^ Fintype.card ι *
      ((Nat.multinomial Finset.univ t : ℝ) * ∏ i, (t i : ℝ) ^ t i) := by
  have hs : ∑ i, (t i : ℝ) = n := by exact_mod_cast ht
  conv_lhs => rw [← hs, Finset.sum_pow_eq_sum_piAntidiag]
  calc
    _ ≤ ∑ _k ∈ Finset.piAntidiag Finset.univ n,
        (Nat.multinomial Finset.univ t : ℝ) * ∏ i, (t i : ℝ) ^ t i := by
      apply Finset.sum_le_sum
      intro k hk
      apply multinomial_term_le_mode
      exact (Finset.mem_piAntidiag.mp hk).1.trans ht.symm
    _ = ((Finset.piAntidiag (Finset.univ : Finset ι) n).card : ℝ) *
        ((Nat.multinomial Finset.univ t : ℝ) * ∏ i, (t i : ℝ) ^ t i) := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_piAntidiag_univ_le (ι := ι) n

section ProductTypes
variable {H : Type u_5} {A : Type u_6} {T : Type u_7} [Fintype H] [DecidableEq H] [Fintype A] [Fintype T]
  [DecidableEq A] [DecidableEq T]

omit [Fintype T] [DecidableEq A] in
lemma card_functionFiber (η : A → T) (k : H → T) :
    Fintype.card {f : H → A // η ∘ f = k} =
      ∏ i, Fintype.card {a : A // η a = k i} := by
  rw [Fintype.card_congr (functionFiberEquiv η k), Fintype.card_pi]

omit [DecidableEq H] in
lemma prod_eq_prod_histogram (f : H → T) (w : T → ℝ) :
    (∏ i, w (f i)) = ∏ t, w t ^ histogram f t := by
  rw [← Fintype.prod_fiberwise f]
  apply Finset.prod_congr rfl
  intro t _
  have he (i : {i // f i = t}) : w (f i.1) = w t := congrArg w i.2
  simp only [he, Finset.prod_const, Finset.card_univ, histogram]

omit [DecidableEq A] in
lemma sum_product_of_types (η : A → T) (q : T → ℝ) (F : (H → T) → ℝ) :
    (∑ f : H → A, F (η ∘ f) * ∏ i, q (η (f i))) =
      ∑ k : H → T, F k * ∏ i, ((Fintype.card {a : A // η a = k i} : ℝ) * q (k i)) := by
  classical
  rw [← Fintype.sum_fiberwise (fun f : H → A => η ∘ f)]
  apply Finset.sum_congr rfl
  intro k _
  have he (f : {f : H → A // η ∘ f = k}) :
      F (η ∘ f.1) * ∏ i, q (η (f.1 i)) = F k * ∏ i, q (k i) := by
    rw [f.2]
    congr 1
    exact Finset.prod_congr rfl (fun i _ => congrArg q (congrFun f.2 i))
  simp_rw [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [card_functionFiber, Nat.cast_prod, Finset.prod_mul_distrib]
  ring

omit [DecidableEq A] in
lemma sum_product_of_type_probabilities (η : A → T) (hη : Function.Surjective η)
    (p : T → ℝ) (F : (H → T) → ℝ) :
    (∑ f : H → A, F (η ∘ f) *
      ∏ i, p (η (f i)) / Fintype.card {a : A // η a = η (f i)}) =
      ∑ k : H → T, F k * ∏ i, p (k i) := by
  rw [sum_product_of_types η
    (fun t => p t / Fintype.card {a : A // η a = t}) F]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  have hn : (Fintype.card {a : A // η a = k i} : ℝ) ≠ 0 := by
    obtain ⟨a, ha⟩ := hη (k i)
    exact_mod_cast ne_of_gt ((Fintype.card_pos_iff (α := {a : A // η a = k i})).mpr ⟨⟨a, ha⟩⟩)
  field_simp

omit [DecidableEq A] in
lemma sum_type_probability_eq_multinomial (η : A → T) (hη : Function.Surjective η)
    (k₀ : H → T) (p : T → ℝ) :
    (∑ f : H → A, (if histogram (η ∘ f) = histogram k₀ then (1 : ℝ) else 0) *
      ∏ i, p (η (f i)) / Fintype.card {a : A // η a = η (f i)}) =
      (Nat.multinomial Finset.univ (histogram k₀) : ℝ) *
        ∏ t, p t ^ histogram k₀ t := by
  classical
  rw [sum_product_of_type_probabilities η hη p
    (fun k => if histogram k = histogram k₀ then 1 else 0)]
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter, ← Finset.sum_subtype_eq_sum_filter]
  simp only [Finset.subtype_univ]
  have he (k : Colorings H T (histogram k₀)) :
      (∏ i, p (k.1 i)) = ∏ t, p t ^ histogram k₀ t := by
    rw [prod_eq_prod_histogram, k.2]
  simp_rw [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    card_colorings_eq_multinomial]

omit [DecidableEq A] in
lemma integer_mean_type_probability_lower (η : A → T) (hη : Function.Surjective η)
    (k₀ : H → T) (hH : 0 < Fintype.card H) :
    1 ≤ (Fintype.card H + 1 : ℝ) ^ Fintype.card T *
      (∑ f : H → A, (if histogram (η ∘ f) = histogram k₀ then (1 : ℝ) else 0) *
        ∏ i, ((histogram k₀ (η (f i)) : ℝ) / Fintype.card H) /
          Fintype.card {a : A // η a = η (f i)}) := by
  classical
  rw [sum_type_probability_eq_multinomial η hη k₀
    (fun t => (histogram k₀ t : ℝ) / Fintype.card H)]
  have hl := multinomial_mode_lower (histogram k₀) (Fintype.card H) (sum_histogram k₀)
  simp_rw [div_pow]
  rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, sum_histogram]
  have hp : (0 : ℝ) < (Fintype.card H : ℝ) ^ Fintype.card H := by positivity
  apply (mul_le_mul_iff_left₀ hp).mp
  field_simp
  nlinarith

end ProductTypes

end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.TableMoments ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10

namespace MatchingSmoothing
open Matrix
section TableKernel
variable {H : Type u_1} {C : Type u_2} [Fintype H] [Fintype C] [DecidableEq H] [DecidableEq C]

omit [DecidableEq C] in

lemma weighted_common_fiber_bound (A : Matrix C C ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (P : (H × Bool → C) → Prop) [DecidablePred P]
    (w : ℝ) (hw : ∀ f, P f → pairWeight A f = w)
    (σ : Equiv.Perm (H × Bool)) :
    (Fintype.card {f : H × Bool → C // P f ∧ P (f ∘ σ)} : ℝ) * w ^ 2 ≤
      ∑ f : H × Bool → C, pairWeight A f * pairWeight A (f ∘ σ) := by
  classical
  calc
    _ = ∑ f : H × Bool → C, if P f ∧ P (f ∘ σ) then w ^ 2 else 0 := by
      rw [← sum_indicator_card]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro f _
      split_ifs <;> simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro f _
      split_ifs with hf
      · rw [hw f hf.1, hw (f ∘ σ) hf.2, pow_two]
      · exact mul_nonneg (pairWeight_nonneg A hA f) (pairWeight_nonneg A hA (f ∘ σ))

omit [DecidableEq C] in
lemma weighted_table_kernel_bound (A : Matrix C C ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (P : (H × Bool → C) → Prop) [DecidablePred P]
    (w Z D L : ℝ) (hw : ∀ f, P f → pairWeight A f = w)
    (hD : 0 < D) (hL : 0 ≤ L) (hz : Z ≤ D ^ 2 * w ^ 2 * L)
    (σ : Equiv.Perm (H × Bool)) :
    Z / D ^ 2 * Fintype.card {f : H × Bool → C // P f ∧ P (f ∘ σ)} ≤
      L * ∑ f : H × Bool → C, pairWeight A f * pairWeight A (f ∘ σ) := by
  have hc := weighted_common_fiber_bound A hA P w hw σ
  have hd : 0 < D ^ 2 := sq_pos_of_pos hD
  have hz' : Z / D ^ 2 ≤ w ^ 2 * L := (div_le_iff₀ hd).mpr (by nlinarith [hz])
  calc
    _ ≤ (w ^ 2 * L) * Fintype.card {f : H × Bool → C // P f ∧ P (f ∘ σ)} :=
      mul_le_mul_of_nonneg_right hz' (Nat.cast_nonneg _)
    _ = L * ((Fintype.card {f : H × Bool → C // P f ∧ P (f ∘ σ)} : ℝ) * w ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hc hL

lemma weighted_table_kernel_moment (A : Matrix C C ℝ)
    (hs : A.IsHermitian) (hA : ∀ i j, 0 ≤ A i j)
    (v : C → ℝ) (hv : ∀ i, 0 < v i) (hAv : A *ᵥ v = v)
    (P : (H × Bool → C) → Prop) [DecidablePred P]
    (w Z D L : ℝ) (hw : ∀ f, P f → pairWeight A f = w)
    (hZ : 0 ≤ Z) (hD : 0 < D) (hL : 0 ≤ L) (hz : Z ≤ D ^ 2 * w ^ 2 * L) :
    (∑ σ : Equiv.Perm (H × Bool),
      (Z / D ^ 2 * Fintype.card {f : H × Bool → C // P f ∧ P (f ∘ σ)}) ^ 2) ≤
      Fintype.card (Equiv.Perm (H × Bool)) * L ^ 2 *
        (Fintype.card H + 1 : ℝ) ^ (Fintype.card C ^ 2) := by
  calc
    _ ≤ ∑ σ : Equiv.Perm (H × Bool),
        (L * ∑ f : H × Bool → C, pairWeight A f * pairWeight A (f ∘ σ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro σ _
      apply pow_le_pow_left₀ (by positivity)
      exact weighted_table_kernel_bound A hA P w Z D L hw hD hL hz σ
    _ = L ^ 2 * ∑ σ : Equiv.Perm (H × Bool),
        (∑ f : H × Bool → C, pairWeight A f * pairWeight A (f ∘ σ)) ^ 2 := by
      simp_rw [mul_pow]
      rw [Finset.mul_sum]
    _ ≤ L ^ 2 * (Fintype.card (Equiv.Perm (H × Bool)) *
        (Fintype.card H + 1 : ℝ) ^ (Fintype.card C ^ 2)) :=
      mul_le_mul_of_nonneg_left (pairWeight_overlap_square_moment A hs hA v hv hAv) (sq_nonneg L)
    _ = _ := by ring

end TableKernel
end MatchingSmoothing

namespace MatchingSmoothing
open Matrix

lemma threeEdgeType_surjective : Function.Surjective threeEdgeType := by decide

lemma card_threeEdgeType_fiber (t : Fin 6) :
    Fintype.card {a : Fin 3 × Fin 3 // threeEdgeType a = t} = typeMultiplicity t := by
  fin_cases t <;> decide

lemma threeEdgeType_symm (a b : Fin 3) : threeEdgeType (a,b) = threeEdgeType (b,a) := by
  fin_cases a <;> fin_cases b <;> rfl

lemma endpoint_type_identity (a b i : Fin 3) :
    (∑ j : Fin 3, (if threeEdgeType (a,b) = threeEdgeType (i,j) then (1 : ℝ) else 0) /
      typeMultiplicity (threeEdgeType (i,j))) =
      ((if a = i then (1 : ℝ) else 0) + (if b = i then 1 else 0)) / 2 := by
  have h0 : typeMultiplicity 0 = 1 := by decide
  have h1 : typeMultiplicity 1 = 2 := by decide
  have h2 : typeMultiplicity 2 = 2 := by decide
  have h3 : typeMultiplicity 3 = 1 := by decide
  have h4 : typeMultiplicity 4 = 2 := by decide
  have h5 : typeMultiplicity 5 = 1 := by decide
  fin_cases a <;> fin_cases b <;> fin_cases i <;>
    norm_num [threeEdgeType, Fin.sum_univ_succ, Fin.ext_iff, h0, h1, h2, h3, h4, h5]

section ThreeTables
variable {H : Type u_3} [Fintype H] [DecidableEq H]

omit [DecidableEq H] in
lemma histogram_cast_sum {V : Type u_4} {T : Type u_5} [Fintype V] [DecidableEq T] (f : V → T) (t : T) :
    (histogram f t : ℝ) = ∑ i, if f i = t then 1 else 0 := by
  classical
  simp only [histogram, Fintype.card_subtype, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> norm_num

omit [DecidableEq H] in
lemma tableGamma_hermitian (f : H × Bool → Fin 3) : (tableGamma f).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff]
  intro i j
  simp only [star_trivial, tableGamma, threeEdgeType_symm j i]

omit [DecidableEq H] in
lemma tableGamma_nonneg (f : H × Bool → Fin 3) : ∀ i j, 0 ≤ tableGamma f i j := by
  intro i j
  unfold tableGamma
  positivity

omit [DecidableEq H] in
lemma tableGamma_rowsum (f : H × Bool → Fin 3) (i : Fin 3) :
    ∑ j, tableGamma f i j = tablePi f i := by
  have he (j : Fin 3) : tableGamma f i j =
      (∑ v : H, (if threeEdgeType (f (v,false),f (v,true)) = threeEdgeType (i,j)
        then (1 : ℝ) else 0) / typeMultiplicity (threeEdgeType (i,j))) / Fintype.card H := by
    simp only [tableGamma, threeTable, histogram_cast_sum, Function.comp_apply,
      pairColorEquiv, Equiv.coe_fn_mk, ← Finset.sum_div]
    ring
  simp_rw [he]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [endpoint_type_identity]
  rw [← Finset.sum_div, div_div]
  congr 1
  simp only [histogram_cast_sum, Fintype.sum_prod_type, Fintype.sum_bool,
    Finset.sum_add_distrib]
  ring

omit [DecidableEq H] in
lemma tablePi_pos (f : H × Bool → Fin 3) (hH : 0 < Fintype.card H)
    (hf : ∀ i, 0 < histogram f i) : ∀ i, 0 < tablePi f i := by
  intro i
  exact div_pos (Nat.cast_pos.mpr (hf i)) (by positivity)

omit [DecidableEq H] in
lemma tablePi_sum (f : H × Bool → Fin 3) (hH : 0 < Fintype.card H) :
    ∑ i, tablePi f i = 1 := by
  simp only [tablePi, ← Finset.sum_div, ← Nat.cast_sum, sum_histogram,
    Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
  field_simp

omit [DecidableEq H] in
lemma pairWeight_tableGamma_eq (f₀ f : H × Bool → Fin 3) :
    pairWeight (tableGamma f₀) f =
      ∏ t : Fin 6, (((threeTable f₀ t : ℝ) / Fintype.card H) / typeMultiplicity t) ^ threeTable f t := by
  exact prod_eq_prod_histogram (threeEdgeType ∘ pairColorEquiv f)
    (fun t => ((threeTable f₀ t : ℝ) / Fintype.card H) / typeMultiplicity t)

omit [DecidableEq H] in
lemma pairWeight_tableGamma_constant (f₀ f : H × Bool → Fin 3)
    (hf : threeTable f = threeTable f₀) :
    pairWeight (tableGamma f₀) f = pairWeight (tableGamma f₀) f₀ := by
  rw [pairWeight_tableGamma_eq, pairWeight_tableGamma_eq, hf]

lemma tableGamma_integer_mean_lower (f₀ : H × Bool → Fin 3) (hH : 0 < Fintype.card H) :
    1 ≤ (Fintype.card H + 1 : ℝ) ^ 6 *
      ((Fintype.card {f : H × Bool → Fin 3 // threeTable f = threeTable f₀} : ℝ) *
        pairWeight (tableGamma f₀) f₀) := by
  classical
  have hl := integer_mean_type_probability_lower threeEdgeType threeEdgeType_surjective
    (threeEdgeType ∘ pairColorEquiv f₀) hH
  simp only [Fintype.card_fin, card_threeEdgeType_fiber] at hl
  have he : (∑ f : H × Bool → Fin 3,
      (if threeTable f = threeTable f₀ then (1 : ℝ) else 0) * pairWeight (tableGamma f₀) f) =
      ∑ k : H → Fin 3 × Fin 3,
      (if histogram (threeEdgeType ∘ k) = threeTable f₀ then (1 : ℝ) else 0) *
        ∏ i, ((threeTable f₀ (threeEdgeType (k i)) : ℝ) / Fintype.card H) /
          typeMultiplicity (threeEdgeType (k i)) := by
    exact Fintype.sum_equiv pairColorEquiv _ _ (fun f => rfl)
  change 1 ≤ (Fintype.card H + 1 : ℝ) ^ 6 *
    (∑ k : H → Fin 3 × Fin 3,
      (if histogram (threeEdgeType ∘ k) = threeTable f₀ then (1 : ℝ) else 0) *
        ∏ i, ((threeTable f₀ (threeEdgeType (k i)) : ℝ) / Fintype.card H) /
          typeMultiplicity (threeEdgeType (k i))) at hl
  rw [← he] at hl
  have hc (f : H × Bool → Fin 3) :
      (if threeTable f = threeTable f₀ then (1 : ℝ) else 0) * pairWeight (tableGamma f₀) f =
        (if threeTable f = threeTable f₀ then (1 : ℝ) else 0) * pairWeight (tableGamma f₀) f₀ := by
    split_ifs with hf
    · rw [pairWeight_tableGamma_constant f₀ f hf]
    · simp
  simp_rw [hc] at hl
  rw [← Finset.sum_mul, sum_indicator_card] at hl
  exact hl

omit [DecidableEq H] in
lemma threeTable_histogram_eq {f g : H × Bool → Fin 3} (hH : 0 < Fintype.card H)
    (h : threeTable f = threeTable g) : histogram f = histogram g := by
  have hγ : tableGamma f = tableGamma g := by
    unfold tableGamma
    rw [h]
  funext i
  have he := (tableGamma_rowsum f i).symm.trans
    ((congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => ∑ j, A i j) hγ).trans
      (tableGamma_rowsum g i))
  change (histogram f i : ℝ) / (2 * Fintype.card H) =
    (histogram g i : ℝ) / (2 * Fintype.card H) at he
  have hn : (2 * Fintype.card H : ℝ) ≠ 0 := by positivity
  exact_mod_cast (div_left_inj' hn).mp he

end ThreeTables

section Probability
variable {V : Type u_6} {C : Type u_7} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C]

lemma histogram_product_mass_le_one (π : C → ℝ) (hn : ∀ i, 0 ≤ π i)
    (hs : ∑ i, π i = 1) (f₀ : V → C) :
    (Fintype.card (Colorings V C (histogram f₀)) : ℝ) * (∏ v, π (f₀ v)) ≤ 1 := by
  classical
  calc
    _ = ∑ f : V → C, if histogram f = histogram f₀ then ∏ v, π (f v) else 0 := by
      have he (f : V → C) :
          (if histogram f = histogram f₀ then ∏ v, π (f v) else 0) =
          (if histogram f = histogram f₀ then (1 : ℝ) else 0) * ∏ v, π (f₀ v) := by
        split_ifs with hf
        · rw [one_mul, prod_eq_prod_histogram f, prod_eq_prod_histogram f₀, hf]
        · simp
      simp_rw [he]
      rw [← Finset.sum_mul, sum_indicator_card]
      congr 1
      exact congrArg Nat.cast (@Fintype.card_congr
        (Colorings V C (histogram f₀)) {f : V → C // histogram f = histogram f₀}
        (coloringsFintype _) (Subtype.fintype _) (Equiv.refl _))
    _ ≤ ∑ f : V → C, ∏ v, π (f v) := by
      apply Finset.sum_le_sum
      intro f _
      split_ifs
      · rfl
      · exact Finset.prod_nonneg (fun v _ => hn (f v))
    _ = ∏ _v : V, ∑ i, π i := Fintype.prod_sum (fun (_v : V) i => π i) |>.symm
    _ = 1 := by simp only [hs, Finset.prod_const_one]

omit [DecidableEq V] [Fintype C] [DecidableEq C] in
lemma vertexSqrtWeight_sq (π : C → ℝ) (hn : ∀ i, 0 ≤ π i) (f : V → C) :
    (∏ v, Real.sqrt (π (f v))) ^ 2 = ∏ v, π (f v) := by
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl (fun v _ => Real.sq_sqrt (hn (f v)))

end Probability

section TableNormalization
variable {H : Type u_8} {C : Type u_9} [Fintype H] [Fintype C] [DecidableEq H] [DecidableEq C]

omit [DecidableEq H] [Fintype C] [DecidableEq C] in
lemma pairWeight_normalized (γ : Matrix C C ℝ) (π : C → ℝ) (f : H × Bool → C) :
    pairWeight (normalizedPairMatrix γ π) f =
      pairWeight γ f / (∏ v : H × Bool, Real.sqrt (π (f v))) := by
  simp only [pairWeight, normalizedPairMatrix, Finset.prod_div_distrib,
    Fintype.prod_prod_type, Fintype.prod_bool]
  congr 1
  exact Finset.prod_congr rfl (fun i _ => mul_comm _ _)

end TableNormalization

section ThreeTableMoment
variable {H : Type u_10} [Fintype H] [DecidableEq H]

lemma three_table_kernel_moment (f₀ : H × Bool → Fin 3) (hH : 0 < Fintype.card H)
    (hf₀ : ∀ i, 0 < histogram f₀ i) :
    (∑ σ : Equiv.Perm (H × Bool),
      ((Fintype.card (Colorings (H × Bool) (Fin 3) (histogram f₀)) : ℝ) /
        (Fintype.card {f : H × Bool → Fin 3 // threeTable f = threeTable f₀} : ℝ) ^ 2 *
        Fintype.card {f : H × Bool → Fin 3 //
          threeTable f = threeTable f₀ ∧ threeTable (f ∘ σ) = threeTable f₀}) ^ 2) ≤
      Fintype.card (Equiv.Perm (H × Bool)) * (Fintype.card H + 1 : ℝ) ^ 33 := by
  classical
  let γ := tableGamma f₀
  let π := tablePi f₀
  let A := normalizedPairMatrix γ π
  let Z : ℝ := Fintype.card (Colorings (H × Bool) (Fin 3) (histogram f₀))
  let D : ℝ := Fintype.card {f : H × Bool → Fin 3 // threeTable f = threeTable f₀}
  let Q := pairWeight γ f₀
  let S := ∏ v : H × Bool, Real.sqrt (π (f₀ v))
  have hπ : ∀ i, 0 < π i := tablePi_pos f₀ hH hf₀
  have hS : 0 < S := Finset.prod_pos (fun v _ => Real.sqrt_pos.mpr (hπ (f₀ v)))
  have hD : 0 < D := by
    change (0 : ℝ) < (Fintype.card {f : H × Bool → Fin 3 // threeTable f = threeTable f₀} : ℝ)
    exact Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨⟨f₀, rfl⟩⟩)
  have hQ : 0 ≤ Q := pairWeight_nonneg γ (tableGamma_nonneg f₀) f₀
  have hw (f : H × Bool → Fin 3) (ht : threeTable f = threeTable f₀) :
      pairWeight A f = Q / S := by
    rw [pairWeight_normalized, pairWeight_tableGamma_constant f₀ f ht]
    congr 1
    change (∏ v, (fun i => Real.sqrt (π i)) (f v)) =
      ∏ v, (fun i => Real.sqrt (π i)) (f₀ v)
    rw [prod_eq_prod_histogram f (fun i => Real.sqrt (π i)),
      prod_eq_prod_histogram f₀ (fun i => Real.sqrt (π i)), threeTable_histogram_eq hH ht]
  have hprob : Z * S ^ 2 ≤ 1 := by
    rw [show S ^ 2 = _ from vertexSqrtWeight_sq π (fun i => (hπ i).le) f₀]
    exact histogram_product_mass_le_one π (fun i => (hπ i).le) (tablePi_sum f₀ hH) f₀
  have hmean : 1 ≤ (Fintype.card H + 1 : ℝ) ^ 6 * (D * Q) :=
    tableGamma_integer_mean_lower f₀ hH
  have hb : (1 : ℝ) ≤ D ^ 2 * Q ^ 2 * (Fintype.card H + 1 : ℝ) ^ 12 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hmean 2
    calc
      (1 : ℝ) = 1 ^ 2 := by norm_num
      _ ≤ ((Fintype.card H + 1 : ℝ) ^ 6 * (D * Q)) ^ 2 := h
      _ = _ := by ring
  have hz : Z ≤ D ^ 2 * (Q / S) ^ 2 * (Fintype.card H + 1 : ℝ) ^ 12 := by
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hS)).mp
    have he : (D ^ 2 * (Q / S) ^ 2 * (Fintype.card H + 1 : ℝ) ^ 12) * S ^ 2 =
        D ^ 2 * Q ^ 2 * (Fintype.card H + 1 : ℝ) ^ 12 := by field_simp
    rw [he]
    linarith
  have hg := weighted_table_kernel_moment A
    (normalizedPairMatrix_hermitian γ π (tableGamma_hermitian f₀))
    (normalizedPairMatrix_nonneg γ π (tableGamma_nonneg f₀))
    (fun i => Real.sqrt (π i)) (fun i => Real.sqrt_pos.mpr (hπ i))
    (normalizedPairMatrix_fixed γ π hπ (tableGamma_rowsum f₀))
    (fun f => threeTable f = threeTable f₀) (Q / S) Z D
    ((Fintype.card H + 1 : ℝ) ^ 12) hw (Nat.cast_nonneg _) hD (by positivity) hz
  convert hg using 1
  norm_num [Fintype.card_fin]
  ring

end ThreeTableMoment
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.IncidenceKernels ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace MatchingSmoothing
open Matrix

section FiniteSums
variable {G : Type u_1} {X : Type u_2} [Fintype G] [Group G] [Fintype X] [MulAction G X]

omit [Fintype G] in
lemma sum_smul_eq (g : G) (f : X → ℝ) : ∑ x, f (g • x) = ∑ x, f x :=
  Equiv.sum_comp (MulAction.toPerm g) f

omit [Fintype X] in
lemma sum_group_smul_eq (x₀ : X) (ht : ∀ x, ∃ g : G, g • x₀ = x)
    (f : X → ℝ) (x : X) : ∑ g : G, f (g • x) = ∑ g : G, f (g • x₀) := by
  obtain ⟨h, rfl⟩ := ht x
  simp_rw [← mul_smul]
  exact Equiv.sum_comp (Equiv.mulRight h) (fun g => f (g • x₀))

lemma group_smul_sum_card (x₀ : X) (ht : ∀ x, ∃ g : G, g • x₀ = x)
    (f : X → ℝ) :
    (Fintype.card G : ℝ) * ∑ x, f x =
      (Fintype.card X : ℝ) * ∑ g : G, f (g • x₀) := by
  calc
    _ = ∑ g : G, ∑ x, f (g • x) := by simp only [sum_smul_eq, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    _ = ∑ x, ∑ g : G, f (g • x) := Finset.sum_comm
    _ = _ := by simp_rw [sum_group_smul_eq x₀ ht, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]

omit [Fintype G] in
lemma invariant_kernel_sum (x₀ : X) (ht : ∀ x, ∃ g : G, g • x₀ = x)
    (K : X → X → ℝ) (hK : ∀ (g : G) x y, K (g • x) (g • y) = K x y) :
    (∑ x, ∑ y, K x y) = (Fintype.card X : ℝ) * ∑ y, K x₀ y := by
  have he (x : X) : ∑ y, K x y = ∑ y, K x₀ y := by
    obtain ⟨g, rfl⟩ := ht x
    rw [← sum_smul_eq g (fun y => K (g • x₀) y)]
    simp_rw [hK]
  simp_rw [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

lemma invariant_kernel_double_sum_group (x₀ : X)
    (ht : ∀ x, ∃ g : G, g • x₀ = x)
    (K : X → X → ℝ) (hK : ∀ (g : G) x y, K (g • x) (g • y) = K x y) :
    (Fintype.card G : ℝ) * (∑ x, ∑ y, K x y) =
      (Fintype.card X : ℝ) ^ 2 * ∑ g : G, K x₀ (g • x₀) := by
  rw [invariant_kernel_sum x₀ ht K hK]
  have h := group_smul_sum_card x₀ ht (K x₀)
  nlinarith [h]

end FiniteSums

section KernelTrace
variable {G : Type u_3} {X : Type u_4} [Fintype G] [Group G] [Fintype X] [DecidableEq X]
  [MulAction G X]

omit [DecidableEq X] in
lemma trace_normalized_kernel_sq (K : Matrix X X ℝ) (hs : ∀ x y, K x y = K y x) :
    Matrix.trace ((Matrix.of fun x y => K x y / Fintype.card X) *
      (Matrix.of fun x y => K x y / Fintype.card X)) =
      (∑ x, ∑ y, K x y ^ 2) / (Fintype.card X : ℝ) ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [hs y x]
  ring

omit [DecidableEq X] in
lemma trace_normalized_invariant_kernel_sq (x₀ : X)
    (ht : ∀ x, ∃ g : G, g • x₀ = x)
    (K : Matrix X X ℝ) (hs : ∀ x y, K x y = K y x)
    (hi : ∀ (g : G) x y, K (g • x) (g • y) = K x y) :
    Matrix.trace ((Matrix.of fun x y => K x y / Fintype.card X) *
      (Matrix.of fun x y => K x y / Fintype.card X)) =
      (∑ g : G, K x₀ (g • x₀) ^ 2) / (Fintype.card G : ℝ) := by
  have : Nonempty X := ⟨x₀⟩
  rw [trace_normalized_kernel_sq K hs]
  have h := invariant_kernel_double_sum_group x₀ ht
    (fun x y => K x y ^ 2) (fun g x y => congrArg (fun a : ℝ => a ^ 2) (hi g x y))
  have hx : (Fintype.card X : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hg : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  apply (div_eq_div_iff (pow_ne_zero _ hx) hg).mpr
  nlinarith [h]

end KernelTrace

section Incidence
variable {X : Type u_5} {Z : Type u_6} [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq Z]

omit [Fintype X] [DecidableEq X] [DecidableEq Z] in
lemma commonIncidence_eq (P : X → Z → Prop) (x y : X) :
    commonIncidence P x y = ∑ z, incidence P z x * incidence P z y := by
  classical
  simp only [commonIncidence, Fintype.card_subtype, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hx : P x z <;> by_cases hy : P y z <;> simp [incidence, hx, hy]

omit [Fintype X] [DecidableEq X] [DecidableEq Z] in
lemma commonIncidence_symm (P : X → Z → Prop) (x y : X) :
    commonIncidence P x y = commonIncidence P y x := by
  simp only [commonIncidence_eq, mul_comm]

omit [Fintype X] [DecidableEq X] [DecidableEq Z] in
lemma incidenceKernel_symm (P : X → Z → Prop) (D : ℝ) (x y : X) :
    incidenceKernel P D x y = incidenceKernel P D y x := by
  unfold incidenceKernel
  rw [commonIncidence_symm P x y]

omit [DecidableEq X] [DecidableEq Z] in
lemma incidenceOperator_eq (P : X → Z → Prop) (D : ℝ) :
    incidenceOperator P D =
      ((Fintype.card Z : ℝ) / (D ^ 2 * Fintype.card X)) •
        ((incidence P).transpose * incidence P) := by
  ext x y
  simp only [incidenceOperator, incidenceKernel, commonIncidence_eq, Matrix.smul_apply,
    smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply]
  ring

omit [DecidableEq X] [DecidableEq Z] in
lemma incidenceOperator_posSemidef (P : X → Z → Prop) (D : ℝ) :
    (incidenceOperator P D).PosSemidef := by
  rw [incidenceOperator_eq]
  apply Matrix.PosSemidef.smul
  · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self (incidence P)
  · positivity

omit [DecidableEq X] [DecidableEq Z] in
lemma conditionalAverage_energy [Nonempty X] [Nonempty Z]
    (P : X → Z → Prop) (D : ℝ) (hD : D ≠ 0) (f : X → ℝ) :
    (∑ z, conditionalAverage P ((Fintype.card X : ℝ) * D / Fintype.card Z) f z ^ 2) /
      Fintype.card Z =
    (∑ x, f x * (incidenceOperator P D *ᵥ f) x) / Fintype.card X := by
  have hx : (Fintype.card X : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hz : (Fintype.card Z : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  change _ = (f ⬝ᵥ (incidenceOperator P D *ᵥ f)) / Fintype.card X
  rw [incidenceOperator_eq, Matrix.smul_mulVec, dotProduct_smul,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  simp only [conditionalAverage, div_pow, ← Finset.sum_div, smul_eq_mul]
  change (∑ z, ((incidence P *ᵥ f) z) ^ 2) /
    (((Fintype.card X : ℝ) * D) ^ 2 / (Fintype.card Z : ℝ) ^ 2) / Fintype.card Z =
    ((Fintype.card Z : ℝ) / (D ^ 2 * Fintype.card X)) *
      (∑ z, (incidence P *ᵥ f) z * (incidence P *ᵥ f) z) / Fintype.card X
  simp only [← pow_two]
  field_simp

end Incidence
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.SpectralMultiplicity ----
namespace OAI

universe u_1

namespace MatchingSmoothing

open scoped RealInnerProductSpace

variable {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma trace_square_eq_sum_eigenvalue_sq (B : Module.End ℝ E) (hB : B.IsSymmetric) :
    LinearMap.trace ℝ E (B * B) =
      ∑ i, (hB.eigenvalues (n := Module.finrank ℝ E) rfl i) ^ 2 := by
  rw [LinearMap.trace_eq_sum_inner _ (hB.eigenvectorBasis rfl)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Module.End.mul_apply, hB.apply_eigenvectorBasis rfl, map_smul,
    real_inner_smul_right, OrthonormalBasis.inner_eq_one, mul_one]
  simp [pow_two]

lemma eigenspace_dim_mul_sq_le_trace_square (B : Module.End ℝ E) (hB : B.IsSymmetric)
    (c : ℝ) :
    (Module.finrank ℝ (Module.End.eigenspace B c) : ℝ) * c ^ 2 ≤
      LinearMap.trace ℝ E (B * B) := by
  classical
  let ev :=  hB.eigenvalues (n := Module.finrank ℝ E) rfl
  let s := Finset.univ.filter fun i => ev i = c
  have hcard : s.card = Module.finrank ℝ (Module.End.eigenspace B c) :=
    hB.card_filter_eigenvalues_eq rfl c
  have he : ∑ i ∈ s, ev i ^ 2 = (s.card : ℝ) * c ^ 2 := by
    calc
      ∑ i ∈ s, ev i ^ 2 = ∑ _i ∈ s, c ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [(Finset.mem_filter.mp hi).2]
      _ = _ := by simp
  rw [trace_square_eq_sum_eigenvalue_sq B hB, ← hcard, ← he]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
    (fun _ _ _ => sq_nonneg _)

lemma quadratic_form_le_of_eigenvalues_le (B : Module.End ℝ E) (hB : B.IsSymmetric)
    (a : ℝ) (ha : ∀ i, hB.eigenvalues (n := Module.finrank ℝ E) rfl i ≤ a)
    (x : E) : ⟪x, B x⟫ ≤ a * ‖x‖ ^ 2 := by
  let b := hB.eigenvectorBasis (n := Module.finrank ℝ E) rfl
  rw [← b.sum_inner_mul_inner x (B x), ← b.sum_sq_inner_right x, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have he : B (b i) = (hB.eigenvalues rfl i) • b i := hB.apply_eigenvectorBasis rfl i
  rw [← hB (b i) x, he, real_inner_smul_left, real_inner_comm x (b i)]
  nlinarith [sq_nonneg (inner ℝ (b i) x), ha i]

lemma quadratic_form_le_of_multiplicity (B : Module.End ℝ E) (hB : B.IsSymmetric)
    (m H a : ℝ) (hm : 0 < m) (ha : 0 ≤ a)
    (hdim : ∀ c : ℝ, c ≠ 0 → Module.End.HasEigenvalue B c →
      m ≤ Module.finrank ℝ (Module.End.eigenspace B c))
    (htrace : LinearMap.trace ℝ E (B * B) ≤ H)
    (hHa : H ≤ m * a ^ 2) (x : E) : ⟪x, B x⟫ ≤ a * ‖x‖ ^ 2 := by
  apply quadratic_form_le_of_eigenvalues_le B hB a _ x
  intro i
  let c := hB.eigenvalues (n := Module.finrank ℝ E) rfl i
  by_cases hc : c = 0
  · simpa only [← show c = hB.eigenvalues rfl i from rfl, hc] using ha
  · have hd := hdim c hc (hB.hasEigenvalue_eigenvalues rfl i)
    have he := eigenspace_dim_mul_sq_le_trace_square B hB c
    have hsq : m * c ^ 2 ≤ m * a ^ 2 :=
      (mul_le_mul_of_nonneg_right hd (sq_nonneg c)).trans (he.trans (htrace.trans hHa))
    have hle : c ^ 2 ≤ a ^ 2 := (mul_le_mul_iff_right₀ hm).mp hsq
    change c ≤ a
    nlinarith

end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.MatchingIncidence ----
namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing

namespace Pairing
variable {V : Type u_1} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
lemma smul_eq_relabel (p : Equiv.Perm V) (M : Pairing V) : p • M = relabel p M := rfl

omit [DecidableEq V] in
lemma table_relabel (p : Equiv.Perm V) (M : Pairing V) (f : V → Fin 3) :
    (relabel p M).table f = M.table (f ∘ p) := by
  funext t
  unfold table
  congr 1
  have he : (fun v => threeEdgeType (f v, f ((relabel p M).1 v))) ∘ p =
      (fun v => threeEdgeType ((f ∘ p) v, (f ∘ p) (M.1 v))) := by
    funext v
    simp only [Function.comp_apply, relabel_apply]
    rw [Equiv.Perm.inv_def, p.symm_apply_apply]
  rw [← he, histogram_comp_perm]

end Pairing

section StandardTable
variable {H : Type u_2} [Fintype H] [DecidableEq H]

omit [DecidableEq H] in
lemma standardPairing_table (f : H × Bool → Fin 3) :
    (standardPairing (H := H)).table f = threeTable f := by
  funext t
  have he : histogram (fun v => threeEdgeType (f v, f ((standardPairing (H := H)).1 v))) t =
      2 * threeTable f t := by
    have hr : (histogram (fun v => threeEdgeType (f v,
        f ((standardPairing (H := H)).1 v))) t : ℝ) = 2 * threeTable f t := by
      simp only [histogram_cast_sum, Fintype.sum_prod_type, Fintype.sum_bool,
        standardPairing, Equiv.prodCongr_apply]
      change (∑ i, ((if threeEdgeType (f (i,true),f (i,false)) = t then (1 : ℝ) else 0) +
        (if threeEdgeType (f (i,false),f (i,true)) = t then 1 else 0))) = _
      simp_rw [threeEdgeType_symm (f (_,true)) (f (_,false))]
      rw [Finset.sum_add_distrib]
      change (∑ i, if threeEdgeType (f (i,false),f (i,true)) = t then (1 : ℝ) else 0) +
        (∑ i, if threeEdgeType (f (i,false),f (i,true)) = t then (1 : ℝ) else 0) = _
      rw [show (threeTable f t : ℝ) =
        ∑ i, if threeEdgeType (f (i,false),f (i,true)) = t then 1 else 0 from
          histogram_cast_sum (threeEdgeType ∘ pairColorEquiv f) t]
      ring
    exact_mod_cast hr
  change _ / 2 = _
  rw [he, Nat.mul_div_right _ (by decide : 0 < 2)]

end StandardTable

section MatchingIncidence
variable {H : Type u_3} [Fintype H] [DecidableEq H]

omit [DecidableEq H] in
lemma commonIncidence_table_relabel (f₀ : H × Bool → Fin 3)
    (p : Equiv.Perm (H × Bool)) (M N : Pairing (H × Bool)) :
    commonIncidence (tableRelation f₀) (Pairing.relabel p M) (Pairing.relabel p N) =
      commonIncidence (tableRelation f₀) M N := by
  classical
  unfold commonIncidence
  congr 1
  apply Fintype.card_congr
  apply (coloringPerm (histogram f₀) p).subtypeEquiv
  intro z
  change ((Pairing.relabel p M).table z.1 = _ ∧ (Pairing.relabel p N).table z.1 = _) ↔
    (M.table (z.1 ∘ p) = _ ∧ N.table (z.1 ∘ p) = _)
  simp only [Pairing.table_relabel]

lemma commonIncidence_standard (f₀ : H × Bool → Fin 3) (hH : 0 < Fintype.card H)
    (p : Equiv.Perm (H × Bool)) :
    commonIncidence (tableRelation f₀) standardPairing (Pairing.relabel p standardPairing) =
      (Fintype.card {f : H × Bool → Fin 3 //
        threeTable f = threeTable f₀ ∧ threeTable (f ∘ p) = threeTable f₀} : ℝ) := by
  classical
  unfold commonIncidence
  congr 1
  apply Fintype.card_congr
  refine { toFun := fun z => ⟨z.1.1, ?_⟩
           invFun := fun f => ⟨⟨f.1, threeTable_histogram_eq hH f.2.1⟩, ?_⟩
           left_inv := fun _ => rfl
           right_inv := fun _ => rfl }
  · simpa only [tableRelation, Pairing.table_relabel, standardPairing_table] using z.2
  · simpa only [tableRelation, Pairing.table_relabel, standardPairing_table] using f.2

lemma matching_table_trace_square (f₀ : H × Bool → Fin 3) (hH : 0 < Fintype.card H)
    (hf₀ : ∀ i, 0 < histogram f₀ i) :
    let D : ℝ := Fintype.card {f : H × Bool → Fin 3 // threeTable f = threeTable f₀}
    Matrix.trace (incidenceOperator (tableRelation f₀) D *
      incidenceOperator (tableRelation f₀) D) ≤ (Fintype.card H + 1 : ℝ) ^ 33 := by
  classical
  dsimp only
  let D : ℝ := Fintype.card {f : H × Bool → Fin 3 // threeTable f = threeTable f₀}
  change Matrix.trace (incidenceOperator (tableRelation f₀) D *
    incidenceOperator (tableRelation f₀) D) ≤ _
  have he := trace_normalized_invariant_kernel_sq (G := Equiv.Perm (H × Bool))
    (standardPairing (H := H)) (fun M => Pairing.exists_relabel _ M)
    (incidenceKernel (tableRelation f₀) D)
    (incidenceKernel_symm (tableRelation f₀) D)
    (fun p M N => by
      change (Fintype.card _ : ℝ) / D ^ 2 * commonIncidence _ (Pairing.relabel p M)
        (Pairing.relabel p N) = (Fintype.card _ : ℝ) / D ^ 2 * commonIncidence _ M N
      rw [commonIncidence_table_relabel])
  change Matrix.trace (incidenceOperator (tableRelation f₀) D *
    incidenceOperator (tableRelation f₀) D) = _ at he
  rw [he]
  have hp : (0 : ℝ) < Fintype.card (Equiv.Perm (H × Bool)) := Nat.cast_pos.mpr Fintype.card_pos
  apply (div_le_iff₀ hp).mpr
  simp only [incidenceKernel, Pairing.smul_eq_relabel,
    commonIncidence_standard f₀ hH]
  exact (three_table_kernel_moment f₀ hH hf₀).trans_eq (mul_comm _ _)

end MatchingIncidence
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.SpectralContraction ----
namespace OAI

universe u_1 u_2

namespace MatchingSmoothing
open scoped RealInnerProductSpace
variable {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma compression_symmetric (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (W : Submodule ℝ E) : (compression A W).IsSymmetric := by
  intro x y
  change ⟪W.orthogonalProjectionOnto (A x), y⟫ =
    ⟪x, W.orthogonalProjectionOnto (A y)⟫
  simpa only [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right] using hA x y

lemma compression_inner (A : Module.End ℝ E) (W : Submodule ℝ E) (x y : W) :
    ⟪x, compression A W y⟫ = ⟪(x : E), A y⟫ :=
  Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left _ _

omit [FiniteDimensional ℝ E] in
lemma trace_square_eq_sum_norm_sq (A : Module.End ℝ E) (hA : A.IsSymmetric)
    {ι : Type u_2} [Fintype ι] (b : OrthonormalBasis ι ℝ E) :
    LinearMap.trace ℝ E (A * A) = ∑ i, ‖A (b i)‖ ^ 2 := by
  rw [LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro i _
  rw [Module.End.mul_apply, ← hA, real_inner_self_eq_norm_sq]

lemma trace_square_compression_le (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (W : Submodule ℝ E) :
    LinearMap.trace ℝ W (compression A W * compression A W) ≤
      LinearMap.trace ℝ E (A * A) := by
  classical
  let b := stdOrthonormalBasis ℝ W
  let e := stdOrthonormalBasis ℝ E
  rw [trace_square_eq_sum_norm_sq _ (compression_symmetric A hA W) b,
    trace_square_eq_sum_norm_sq A hA e]
  calc
    ∑ i, ‖compression A W (b i)‖ ^ 2 ≤ ∑ i, ‖A (b i)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr
        (W.norm_orthogonalProjectionOnto_apply_le _)
    _ = ∑ i, ∑ j, ⟪e j, A (b i)⟫ ^ 2 := by
      simp_rw [e.sum_sq_inner_right]
    _ = ∑ j, ∑ i, ⟪(b i : E), A (e j)⟫ ^ 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      rw [← hA, real_inner_comm]
    _ ≤ ∑ j, ‖A (e j)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      have hb := b.orthonormal.comp_linearIsometry W.subtypeₗᵢ
      have hh := hb.sum_inner_products_le (A (e j)) (s := Finset.univ)
      simpa only [Function.comp_apply, Submodule.coe_subtypeₗᵢ, Submodule.coe_subtype, Real.norm_eq_abs, sq_abs] using hh

end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.EquivariantCompression ----
namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing
namespace Pairing
variable {V : Type u_1}

lemma act_pointwise_mul (p : Equiv.Perm V) (f g : Pairing V → ℝ) :
    act p (f * g) = act p f * act p g := rfl

lemma act_pointwise_one (p : Equiv.Perm V) : act p (1 : Pairing V → ℝ) = 1 := rfl

lemma act_edgeCoord (p : Equiv.Perm V) (e : V × V) :
    act p (edgeCoord e) = edgeCoord (p e.1, p e.2) := by
  classical
  ext M
  simp only [act_apply, edgeCoord, relabel_apply, inv_inv]
  congr 1
  exact propext p.symm_apply_eq

lemma lowDegree_invariant (p : Equiv.Perm V) (d : ℕ)
    (f : Pairing V → ℝ) (hf : f ∈ lowDegree edgeCoord d) :
    act p f ∈ lowDegree edgeCoord d := by
  apply Submodule.span_induction (p := fun f _ => act p f ∈ lowDegree edgeCoord d)
    _ _ _ _ hf
  · rintro f ⟨l, hl, rfl⟩
    have hprod : act p ((l.map edgeCoord).prod) =
        ((l.map (fun e => (p e.1, p e.2))).map edgeCoord).prod := by
      clear hl
      induction l with
      | nil => exact act_pointwise_one p
      | cons e l ih =>
        simp only [List.map_cons, List.prod_cons, act_pointwise_mul,
          act_edgeCoord, ih]
    rw [hprod]
    exact Submodule.subset_span ⟨_, by simpa, rfl⟩
  · simp
  · intro f g _ _ hf hg
    simpa only [map_add] using (lowDegree edgeCoord d).add_mem hf hg
  · intro c f _ hf
    simpa only [map_smul] using (lowDegree edgeCoord d).smul_mem c hf

end Pairing

open scoped RealInnerProductSpace
section EuclideanPermutations
variable {X : Type u_2} [Fintype X]

lemma matrix_equivariant [DecidableEq X] (A : Matrix X X ℝ) (e : Equiv.Perm X)
    (hA : ∀ x y, A (e x) (e y) = A x y) (v : EuclideanSpace ℝ X) :
    A.toEuclideanLin (permIso e v) = permIso e (A.toEuclideanLin v) := by
  ext x
  change (∑ y, A x y * v (e.symm y)) = ∑ y, A (e.symm x) y * v y
  rw [← Equiv.sum_comp e (fun y => A x y * v (e.symm y))]
  apply Finset.sum_congr rfl
  intro y _
  rw [e.symm_apply_apply, ← hA (e.symm x) y, e.apply_symm_apply]

lemma matrix_trace_square [DecidableEq X] (A : Matrix X X ℝ) :
    LinearMap.trace ℝ (EuclideanSpace ℝ X) (A.toEuclideanLin * A.toEuclideanLin) =
      Matrix.trace (A * A) := by
  simp only [Matrix.toLpLin_eq_toLin, Module.End.mul_eq_comp,
    ← Matrix.toLin_mul, Matrix.trace_toLin_eq]

end EuclideanPermutations

section CompressionEquivariance
variable {E : Type u_3} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma invariant_orthogonal (W : Submodule ℝ E) (e : E ≃ₗᵢ[ℝ] E)
    (hi : ∀ x, x ∈ W → e.symm x ∈ W) (x : E) (hx : x ∈ Wᗮ) :
    e x ∈ Wᗮ := by
  rw [Submodule.mem_orthogonal] at hx ⊢
  intro y hy
  rw [← e.apply_symm_apply y, e.inner_map_map]
  exact hx (e.symm y) (hi y hy)

lemma starProjection_equivariant (W : Submodule ℝ E) (e : E ≃ₗᵢ[ℝ] E)
    (h : ∀ x, x ∈ W → e x ∈ W) (hi : ∀ x, x ∈ W → e.symm x ∈ W)
    (x : E) : e (W.starProjection x) = W.starProjection (e x) := by
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact h _ (W.orthogonalProjectionOnto x).property
  · intro y hy
    rw [← e.apply_symm_apply y, ← e.map_sub, e.inner_map_map]
    exact W.starProjection_inner_eq_zero x (e.symm y) (hi y hy)

lemma compression_eigenspace_invariant (A : Module.End ℝ E) (W : Submodule ℝ E)
    (e : E ≃ₗᵢ[ℝ] E) (h : ∀ x, x ∈ W → e x ∈ W)
    (hi : ∀ x, x ∈ W → e.symm x ∈ W)
    (hA : ∀ x, A (e x) = e (A x)) (c : ℝ) (x : E)
    (hx : x ∈ (Module.End.eigenspace (compression A W) c).map W.subtype) :
    e x ∈ (Module.End.eigenspace (compression A W) c).map W.subtype := by
  rcases hx with ⟨x, hx, rfl⟩
  refine ⟨⟨e x, h x x.2⟩, ?_, rfl⟩
  simp only [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hx ⊢
  apply Subtype.ext
  have he := congrArg (fun y : W => (y : E)) hx
  change W.starProjection (A x) = c • (x : E) at he
  change W.starProjection (A (e (x : E))) = c • e (x : E)
  rw [hA, ← starProjection_equivariant W e h hi, he, map_smul]

end CompressionEquivariance
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.PolynomialSpaces ----
namespace OAI

namespace MatchingSmoothing
open scoped RealInnerProductSpace

lemma matchingEquiv_relabel {h : ℕ} (p : Equiv.Perm (Vertices h)) (f : MatchingSpace h) :
    matchingEquiv h (relabelIso p f) = Pairing.act p (matchingEquiv h f) := rfl

lemma relabelIso_symm {h : ℕ} (p : Equiv.Perm (Vertices h)) :
    (relabelIso p).symm = relabelIso p⁻¹ := by
  simp only [relabelIso, permIso, LinearIsometryEquiv.piLpCongrLeft_symm]
  congr 1

lemma polynomialSpace_invariant {h d : ℕ} (p : Equiv.Perm (Vertices h))
    (f : MatchingSpace h) (hf : f ∈ polynomialSpace h d) :
    relabelIso p f ∈ polynomialSpace h d :=
  Pairing.lowDegree_invariant p d _ hf

lemma highSpace_invariant {h d : ℕ} (p : Equiv.Perm (Vertices h))
    (f : MatchingSpace h) (hf : f ∈ (polynomialSpace h d)ᗮ) :
    relabelIso p f ∈ (polynomialSpace h d)ᗮ := by
  apply invariant_orthogonal (polynomialSpace h d) (relabelIso p) _ f hf
  intro x hx
  rw [relabelIso_symm]
  exact polynomialSpace_invariant p⁻¹ x hx

lemma euclidean_high_degree_dimension {h : ℕ} (k : ℕ) (hk : 4*k < h)
    (W : Submodule ℝ (MatchingSpace h))
    (hW : ∀ p f, f ∈ W → relabelIso p f ∈ W)
    (hle : W ≤ (polynomialSpace h ((4*k)*(4*k)))ᗮ)
    (hne : ∃ f ∈ W, f ≠ 0) : h.choose k ≤ Module.finrank ℝ W := by
  let l := matchingEquiv h
  have he := invariant_high_degree_dimension k hk (W.map l.toLinearMap)
  have hinv (p : Equiv.Perm (Vertices h)) (f : Pairing (Vertices h) → ℝ)
      (hf : f ∈ W.map l.toLinearMap) : Pairing.act p f ∈ W.map l.toLinearMap := by
    rcases hf with ⟨x, hx, rfl⟩
    exact ⟨relabelIso p x, hW p x hx, matchingEquiv_relabel p x⟩
  have hdis : Disjoint (W.map l.toLinearMap)
      (lowDegree Pairing.edgeCoord ((4*k)*(4*k))) := by
    rw [Submodule.disjoint_def]
    rintro f ⟨x, hx, rfl⟩ hp
    have hp' : x ∈ polynomialSpace h ((4*k)*(4*k)) := hp
    have hx0 := Submodule.disjoint_def.mp
      (polynomialSpace h ((4*k)*(4*k))).orthogonal_disjoint.symm x (hle hx) hp'
    rw [hx0, map_zero]
  have hn : ∃ f ∈ W.map l.toLinearMap, f ≠ 0 := by
    obtain ⟨x, hx, hx0⟩ := hne
    refine ⟨l x, ⟨x, hx, rfl⟩, ?_⟩
    simpa using hx0
  simpa only [LinearEquiv.finrank_map_eq] using he hinv hdis hn

lemma matching_compression_multiplicity {h : ℕ} (k : ℕ) (hk : 4*k < h)
    (A : Module.End ℝ (MatchingSpace h))
    (hA : ∀ p x, A (relabelIso p x) = relabelIso p (A x))
    (c : ℝ) (hc : Module.End.HasEigenvalue
      (compression A (polynomialSpace h ((4*k)*(4*k)))ᗮ) c) :
    h.choose k ≤ Module.finrank ℝ (Module.End.eigenspace
      (compression A (polynomialSpace h ((4*k)*(4*k)))ᗮ) c) := by
  let W := (polynomialSpace h ((4*k)*(4*k)))ᗮ
  let U := (Module.End.eigenspace (compression A W) c).map W.subtype
  have hinv : ∀ p x, x ∈ U → relabelIso p x ∈ U := by
    intro p x hx
    apply compression_eigenspace_invariant A W (relabelIso p)
      (highSpace_invariant p) _ (hA p) c x hx
    intro y hy
    rw [relabelIso_symm]
    exact highSpace_invariant p⁻¹ y hy
  have hle : U ≤ W := by
    rintro x ⟨x, _, rfl⟩
    exact x.2
  have hne : ∃ x ∈ U, x ≠ 0 := by
    obtain ⟨x, hx, hx0⟩ := hc.exists_hasEigenvector
    refine ⟨x, ⟨x, hx, rfl⟩, ?_⟩
    intro he
    exact hx0 (Subtype.ext he)
  have hd := euclidean_high_degree_dimension k hk U hinv hle hne
  simpa only [U, Submodule.finrank_map_subtype_eq] using hd

lemma symmetric_matching_smoothing {h : ℕ} (k : ℕ) (hk : 4*k < h)
    (A : Matrix (Pairing (Vertices h)) (Pairing (Vertices h)) ℝ)
    (hA : A.IsHermitian)
    (heq : ∀ p M N, A (Pairing.relabel p M) (Pairing.relabel p N) = A M N)
    (H a : ℝ) (ha : 0 ≤ a)
    (htrace : Matrix.trace (A * A) ≤ H)
    (hHa : H ≤ (h.choose k : ℝ) * a ^ 2)
    (f : MatchingSpace h) (hf : f ∈ (polynomialSpace h ((4*k)*(4*k)))ᗮ) :
    ⟪f, A.toEuclideanLin f⟫ ≤ a * ‖f‖ ^ 2 := by
  classical
  let W := (polynomialSpace h ((4*k)*(4*k)))ᗮ
  have hm : (0 : ℝ) < h.choose k := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  have hs : A.toEuclideanLin.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hd (c : ℝ) (_hc : c ≠ 0)
      (he : Module.End.HasEigenvalue (compression A.toEuclideanLin W) c) :
      (h.choose k : ℝ) ≤ Module.finrank ℝ
        (Module.End.eigenspace (compression A.toEuclideanLin W) c) := by
    exact_mod_cast matching_compression_multiplicity k hk A.toEuclideanLin
      (fun p x => matrix_equivariant A (Pairing.relabelEquiv p) (heq p) x) c he
  have ht : LinearMap.trace ℝ W (compression A.toEuclideanLin W *
      compression A.toEuclideanLin W) ≤ H := by
    apply (trace_square_compression_le A.toEuclideanLin hs W).trans
    rwa [matrix_trace_square]
  have hh := quadratic_form_le_of_multiplicity (compression A.toEuclideanLin W)
    (compression_symmetric A.toEuclideanLin hs W) (h.choose k) H a hm ha hd ht hHa ⟨f, hf⟩
  simpa only [compression_inner, ← Submodule.norm_coe] using hh

end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.FiberAverages ----
namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing
open Matrix
attribute [local instance] Classical.propDecidable
section FiberAverages
variable {X : Type u_1} {Z : Type u_2} [Fintype X] [Fintype Z]

lemma cardinal_fibers_balance (P : X → Z → Prop) (D E : ℕ)
    (hD : ∀ x, Fintype.card {z // P x z} = D)
    (hE : ∀ z, Fintype.card {x // P x z} = E) :
    Fintype.card X * D = Fintype.card Z * E := by
  classical
  calc
    _ = ∑ x : X, Fintype.card {z // P x z} := by simp [hD]
    _ = ∑ z : Z, Fintype.card {x // P x z} := by
      simp only [Fintype.card_subtype, Finset.card_filter]
      exact Finset.sum_comm
    _ = _ := by simp [hE]

end FiberAverages

section TableFibers
variable {H : Type u_3} [Fintype H] [DecidableEq H]

lemma table_row_card (f₀ : H × Bool → Fin 3) (hH : 0 < Fintype.card H)
    (M : Pairing (H × Bool)) :
    Fintype.card {z // tableRelation f₀ M z} =
      Fintype.card {f : H × Bool → Fin 3 // threeTable f = threeTable f₀} := by
  classical
  obtain ⟨p, rfl⟩ := Pairing.exists_relabel (standardPairing (H := H)) M
  apply Fintype.card_congr
  refine ((coloringPerm (histogram f₀) p).subtypeEquiv
    (q := tableRelation f₀ standardPairing) (fun z => ?_)).trans ?_
  · change ((Pairing.relabel p standardPairing).table z.1 = _) ↔
      (standardPairing.table (z.1 ∘ p) = _)
    rw [Pairing.table_relabel]
  · refine { toFun := fun z => ⟨z.1.1, ?_⟩
             invFun := fun f => ⟨⟨f.1, threeTable_histogram_eq hH f.2⟩, ?_⟩
             left_inv := fun _ => rfl
             right_inv := fun _ => rfl }
    · simpa only [tableRelation, standardPairing_table] using z.2
    · simpa only [tableRelation, standardPairing_table] using f.2

omit [DecidableEq H] in
lemma table_col_card (f₀ : H × Bool → Fin 3)
    (z w : Colorings (H × Bool) (Fin 3) (histogram f₀)) :
    Fintype.card {M // tableRelation f₀ M z} =
      Fintype.card {M // tableRelation f₀ M w} := by
  classical
  let p := permOfHistogram (z.2.trans w.2.symm)
  have hp : w.1 ∘ p = z.1 := funext (permOfHistogram_spec _)
  apply Fintype.card_congr
  apply (Pairing.relabelEquiv p).subtypeEquiv
  intro M
  change (M.table z.1 = _) ↔ ((Pairing.relabel p M).table w.1 = _)
  rw [Pairing.table_relabel, hp]

lemma table_fiber_size (f₀ : H × Bool → Fin 3) (hH : 0 < Fintype.card H)
    (z : Colorings (H × Bool) (Fin 3) (histogram f₀)) :
    (Fintype.card {M // tableRelation f₀ M z} : ℝ) =
      (Fintype.card (Pairing (H × Bool)) : ℝ) *
        Fintype.card {f : H × Bool → Fin 3 // threeTable f = threeTable f₀} /
        Fintype.card (Colorings (H × Bool) (Fin 3) (histogram f₀)) := by
  classical
  have : Nonempty (Colorings (H × Bool) (Fin 3) (histogram f₀)) := ⟨⟨f₀, rfl⟩⟩
  have he := cardinal_fibers_balance (tableRelation f₀) _ _
    (table_row_card f₀ hH) (fun w => table_col_card f₀ w z)
  apply (eq_div_iff (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)).mpr
  have hr : (Fintype.card (Pairing (H × Bool)) : ℝ) *
      Fintype.card {f : H × Bool → Fin 3 // threeTable f = threeTable f₀} =
      Fintype.card (Colorings (H × Bool) (Fin 3) (histogram f₀)) *
        Fintype.card {M // tableRelation f₀ M z} := by exact_mod_cast he
  rw [mul_comm]
  exact hr.symm

end TableFibers

open scoped RealInnerProductSpace
lemma table_smoothing_bound {h : ℕ} (k : ℕ) (hk : 4*k < h)
    (f₀ : Vertices h → Fin 3) (hf₀ : ∀ i, 0 < histogram f₀ i)
    (a : ℝ) (ha : 0 ≤ a) (hHa : (h+1 : ℝ)^33 ≤ (h.choose k : ℝ) * a^2)
    (f : MatchingSpace h) (hf : f ∈ (polynomialSpace h ((4*k)*(4*k)))ᗮ) :
    (∑ z, fiberAverage (tableRelation f₀) (matchingEquiv h f) z ^ 2) /
      Fintype.card (Colorings (Vertices h) (Fin 3) (histogram f₀)) ≤
    a * ((∑ M, (f M)^2) / Fintype.card (Pairing (Vertices h))) := by
  classical
  have hH : 0 < Fintype.card (Fin h) := by simpa using (show 0 < h by omega)
  have : Nonempty (Pairing (Vertices h)) := ⟨standardPairing⟩
  have : Nonempty (Colorings (Vertices h) (Fin 3) (histogram f₀)) := ⟨⟨f₀, rfl⟩⟩
  let D : ℝ := Fintype.card {f : Vertices h → Fin 3 // threeTable f = threeTable f₀}
  have hD : D ≠ 0 := by
    have : Nonempty {f : Vertices h → Fin 3 // threeTable f = threeTable f₀} := ⟨⟨f₀, rfl⟩⟩
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have he : (∑ z, fiberAverage (tableRelation f₀) (matchingEquiv h f) z ^ 2) /
      Fintype.card (Colorings (Vertices h) (Fin 3) (histogram f₀)) =
      (∑ M, f M * (incidenceOperator (tableRelation f₀) D *ᵥ (matchingEquiv h f)) M) /
        Fintype.card (Pairing (Vertices h)) := by
    simp only [fiberAverage, table_fiber_size f₀ hH]
    exact conditionalAverage_energy _ D hD _
  rw [he]
  have hb := symmetric_matching_smoothing k hk (incidenceOperator (tableRelation f₀) D)
    (incidenceOperator_posSemidef _ _).isHermitian
    (fun p M N => by
      simp only [incidenceOperator, incidenceKernel, commonIncidence_table_relabel])
    ((h+1)^33) a ha (by simpa using matching_table_trace_square f₀ hH hf₀) hHa f hf
  rw [EuclideanSpace.real_norm_sq_eq] at hb
  have hinner : ⟪f, (incidenceOperator (tableRelation f₀) D).toEuclideanLin f⟫ =
      ∑ M, f M * (incidenceOperator (tableRelation f₀) D *ᵥ (matchingEquiv h f)) M := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    exact dotProduct_comm _ _
  rw [hinner] at hb
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hb
    (show (0 : ℝ) ≤ Fintype.card (Pairing (Vertices h)) by positivity)

end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.ScalarSmoothing ----
namespace OAI

namespace MatchingSmoothing
open Filter Asymptotics

lemma eventually_power_le_choose (m k : ℕ) (hm : m < k) (c : ℝ) :
    ∀ᶠ h : ℕ in atTop, c * (h : ℝ)^m ≤ (h.choose k : ℝ) := by
  have ho : (fun h : ℕ => (h : ℝ)^m) =o[atTop] (fun h : ℕ => (h : ℝ)^k) :=
    (isLittleO_pow_pow_atTop_of_lt hm).comp_tendsto tendsto_natCast_atTop_atTop
  have hb := ((ho.const_mul_left c).trans_isBigO (isTheta_choose k).symm.isBigO).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hb] with h hh
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ h.choose k by positivity), one_mul] using hh)

lemma eventually_table_moment_small (K : ℕ) :
    ∀ᶠ h : ℕ in atTop, 4*(4*K+34) < h ∧
      (h+1 : ℝ)^33 ≤ (h.choose (4*K+34) : ℝ) * ((2*h : ℝ)^(2*K))⁻¹^2 := by
  have hb := eventually_power_le_choose (33+4*K) (4*K+34) (by omega)
    ((2 : ℝ)^(33+4*K))
  filter_upwards [hb, eventually_gt_atTop (4*(4*K+34))] with h hh hk
  refine ⟨hk, ?_⟩
  have hp : (0 : ℝ) < 2*h := by
    have : 0 < h := by omega
    positivity
  have h1 : (1 : ℝ) ≤ h := by exact_mod_cast (show 1 ≤ h by omega)
  rw [inv_pow, le_mul_inv_iff₀ (pow_pos (pow_pos hp _) _)]
  calc
    (h+1 : ℝ)^33 * ((2*h : ℝ)^(2*K))^2 ≤
        (2*h : ℝ)^33 * ((2*h : ℝ)^(2*K))^2 := by gcongr; linarith
    _ = (2*h : ℝ)^(33+4*K) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    _ ≤ (h.choose (4*K+34) : ℝ) := by simpa only [mul_pow] using hh

lemma residual_mem_high (h d : ℕ) (f : MatchingSpace h) :
    f - polynomialProjection h d f ∈ (polynomialSpace h d)ᗮ := by
  exact (polynomialSpace h d).sub_starProjection_mem_orthogonal f

lemma residual_norm_le (h d : ℕ) (f : MatchingSpace h) :
    ‖f - polynomialProjection h d f‖ ≤ ‖f‖ := by
  rw [polynomialProjection, ← Submodule.starProjection_orthogonal_val]
  exact (polynomialSpace h d)ᗮ.norm_starProjection_apply_le f

lemma uniform_table_smoothing (K : ℕ) :
    ∃ d H : ℕ, 0 < d ∧ ∀ h : ℕ, H ≤ h →
      ∀ (f₀ : Vertices h → Fin 3), (∀ i, 0 < histogram f₀ i) →
      ∀ f : MatchingSpace h,
      (∑ z, fiberAverage (tableRelation f₀)
        (matchingEquiv h (f - polynomialProjection h d f)) z ^ 2) /
        Fintype.card (Colorings (Vertices h) (Fin 3) (histogram f₀)) ≤
      ((2*h : ℝ)^(2*K))⁻¹ *
        ((∑ M, (f M)^2) / Fintype.card (Pairing (Vertices h))) := by
  obtain ⟨H, hH⟩ := eventually_atTop.mp (eventually_table_moment_small K)
  let k := 4*K+34
  let d := (4*k)*(4*k)
  refine ⟨d, H, by dsimp [d, k]; positivity, ?_⟩
  intro h hh f₀ hf₀ f
  obtain ⟨hk, hb⟩ := hH h hh
  apply (table_smoothing_bound k hk f₀ hf₀ _ (by positivity) hb
    _ (residual_mem_high h d f)).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [← EuclideanSpace.real_norm_sq_eq, ← EuclideanSpace.real_norm_sq_eq]
  exact pow_le_pow_left₀ (norm_nonneg _) (residual_norm_le h d f) _

end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.EdgeMonomials ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing
attribute [local instance] Classical.propDecidable
namespace Pairing
variable {V : Type u_1}

lemma mem_edgeSupport (l : List (V × V)) (v : V) :
    v ∈ edgeSupport l ↔ ∃ e ∈ l, v = e.1 ∨ v = e.2 := by
  simp only [edgeSupport, Finset.mem_union, Finset.mem_image, List.mem_toFinset]
  constructor
  · rintro (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩)
    · exact ⟨e, he, Or.inl rfl⟩
    · exact ⟨e, he, Or.inr rfl⟩
  · rintro ⟨e, he, h | h⟩
    · exact Or.inl ⟨e, he, h.symm⟩
    · exact Or.inr ⟨e, he, h.symm⟩

lemma edgeMonomial_eq_indicator (l : List (V × V)) (M : Pairing V) :
    edgeMonomial l M = if ContainsList M l then 1 else 0 := by
  induction l with
  | nil => simp [edgeMonomial, ContainsList]
  | cons e l ih =>
    simp only [edgeMonomial, List.map_cons, List.prod_cons, Pi.mul_apply] at ih ⊢
    rw [ih]
    simp only [ContainsList, List.mem_cons, forall_eq_or_imp, edgeCoord]
    split_ifs <;> simp_all

lemma edgeMonomial_cons (e : V × V) (l : List (V × V)) :
    edgeMonomial (e::l) = edgeCoord e * edgeMonomial l := by
  simp [edgeMonomial]

lemma contains_partner_support {M : Pairing V} {l : List (V × V)}
    (hm : ContainsList M l) {v : V} (hv : v ∈ edgeSupport l) :
    M.1 v ∈ edgeSupport l := by
  obtain ⟨e, he, rfl | rfl⟩ := (mem_edgeSupport l v).mp hv
  · rw [hm e he]
    exact (mem_edgeSupport l e.2).mpr ⟨e, he, Or.inr rfl⟩
  · rw [(partner_eq_iff M e.1 e.2).mp (hm e he)]
    exact (mem_edgeSupport l e.1).mpr ⟨e, he, Or.inl rfl⟩

lemma contains_agree_support {M N : Pairing V} {l : List (V × V)}
    (hm : ContainsList M l) (hn : ContainsList N l) {v : V}
    (hv : v ∈ edgeSupport l) : M.1 v = N.1 v := by
  obtain ⟨e, he, rfl | rfl⟩ := (mem_edgeSupport l v).mp hv
  · rw [hm e he, hn e he]
  · rw [(partner_eq_iff M e.1 e.2).mp (hm e he),
      (partner_eq_iff N e.1 e.2).mp (hn e he)]

lemma redundant_edgeMonomial {M : Pairing V} {e : V × V} {l : List (V × V)}
    (he : M.1 e.1 = e.2) (hm : ContainsList M l)
    (hv : e.1 ∈ edgeSupport l ∨ e.2 ∈ edgeSupport l) :
    edgeMonomial (e::l) = edgeMonomial l := by
  funext N
  simp only [edgeMonomial_eq_indicator]
  congr 1
  simp only [ContainsList, List.mem_cons, forall_eq_or_imp]
  apply propext
  refine and_iff_right_of_imp ?_
  intro hn
  change ContainsList N l at hn
  rcases hv with hv | hv
  · exact (contains_agree_support hn hm hv).trans he
  · apply (partner_eq_iff N e.1 e.2).mpr
    exact (contains_agree_support hn hm hv).trans ((partner_eq_iff M e.1 e.2).mp he)

lemma edgeMonomial_zero_of_unsatisfiable (l : List (V × V))
    (h : ¬ ∃ M : Pairing V, ContainsList M l) : edgeMonomial l = 0 := by
  funext M
  rw [edgeMonomial_eq_indicator, ite_eq_right (fun hm => h ⟨M, hm⟩)]
  rfl

lemma edgeMonomial_act_fix (l : List (V × V)) (p : Equiv.Perm V)
    (hp : ∀ v ∈ edgeSupport l, p v = v) : act p (edgeMonomial l) = edgeMonomial l := by
  funext M
  simp only [act_apply, edgeMonomial_eq_indicator]
  congr 1
  apply propext
  apply forall₂_congr
  intro e he
  have h₁ := hp e.1 ((mem_edgeSupport l e.1).mpr ⟨e, he, Or.inl rfl⟩)
  have h₂ := hp e.2 ((mem_edgeSupport l e.2).mpr ⟨e, he, Or.inr rfl⟩)
  simp only [relabel_apply, inv_inv]
  rw [h₁, Equiv.Perm.inv_def, p.symm_apply_eq, h₂]

end Pairing

section ColorAverage
variable {V : Type u_2} {C : Type u_3} [Fintype V]

lemma colorAverage_apply (z : V → C) (f : Pairing V → ℝ) (M : Pairing V) :
    colorAverage z f M =
      (∑ p : colorStabilizer z, Pairing.act p.1 f M) / Fintype.card (colorStabilizer z) := by
  simp [colorAverage, div_eq_mul_inv, mul_comm]

lemma colorAverage_act (z : V → C) (q : colorStabilizer z) (f : Pairing V → ℝ) :
    colorAverage z (Pairing.act q.1 f) = colorAverage z f := by
  funext M
  simp only [colorAverage_apply, ← Pairing.act_mul]
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight q) (fun p : colorStabilizer z => Pairing.act p.1 f M)

lemma colorAverage_one (z : V → C) : colorAverage z (1 : Pairing V → ℝ) = 1 := by
  funext M
  simp [colorAverage_apply, Pairing.act_apply, Fintype.card_ne_zero]

lemma colorAverage_mul_invariant (z : V → C) (f g : Pairing V → ℝ)
    (hf : ∀ p : colorStabilizer z, Pairing.act p.1 f = f) :
    colorAverage z (f*g) = f * colorAverage z g := by
  funext M
  simp only [colorAverage_apply, Pi.mul_apply, Pairing.act_apply]
  have h (p : colorStabilizer z) : f (Pairing.relabel p.1⁻¹ M) = f M := congrFun (hf p) M
  simp_rw [h, ← Finset.mul_sum, mul_div_assoc]

end ColorAverage
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.PartialColorings ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_1 u_2

namespace MatchingSmoothing
attribute [local instance] Classical.propDecidable
section ColorCounting
variable {V : Type u_1} {C : Type u_2} [Fintype V]

omit [Fintype V] in
lemma swap_preserves_color (z : V → C) {a b : V} (hab : z a = z b) (v : V) :
    z (Equiv.swap a b v) = z v := by
  by_cases hva : v = a
  · subst v; simpa using hab.symm
  by_cases hvb : v = b
  · subst v; simpa using hab
  rw [Equiv.swap_apply_of_ne_of_ne hva hvb]

omit [Fintype V] in
lemma swap_fixes_finset (U : Finset V) {a b : V} (ha : a ∉ U) (hb : b ∉ U)
    (v : V) (hv : v ∈ U) : Equiv.swap a b v = v :=
  Equiv.swap_apply_of_ne_of_ne (fun h => ha (h ▸ hv)) (fun h => hb (h ▸ hv))

omit [Fintype V] in
lemma exists_color_perm_fixing_pair (z : V → C) (U : Finset V)
    {a b c d : V} (ha : a ∉ U) (hb : b ∉ U) (hc : c ∉ U) (hd : d ∉ U)
    (hab : a ≠ b) (hcd : c ≠ d) (hzac : z a = z c) (hzbd : z b = z d) :
    ∃ p : colorStabilizer z, (∀ v ∈ U, p.1 v = v) ∧ p.1 a = c ∧ p.1 b = d := by
  let q := Equiv.swap a c
  have hq : ∀ v, z (q v) = z v := swap_preserves_color z hzac
  have hqfix : ∀ v ∈ U, q v = v := swap_fixes_finset U ha hc
  have hqb : q b ∉ U := by
    intro h
    have hh := hqfix (q b) h
    have : b = q b := by simpa only [q, Equiv.swap_apply_self] using hh
    exact hb (this ▸ h)
  let p := Equiv.swap (q b) d * q
  have hp : p ∈ colorStabilizer z := by
    intro v
    change z (Equiv.swap (q b) d (q v)) = z v
    rw [swap_preserves_color z ((hq b).trans hzbd), hq]
  refine ⟨⟨p, hp⟩, ?_, ?_, ?_⟩
  · intro v hv
    change Equiv.swap (q b) d (q v) = v
    rw [hqfix v hv, swap_fixes_finset U hqb hd v hv]
  · change Equiv.swap (q b) d (q a) = c
    have hqbc : q b ≠ c := by
      change Equiv.swap a c b ≠ c
      intro h
      have hh := congrArg (Equiv.swap a c) h
      have : b = a := by simpa using hh
      exact hab this.symm
    rw [show q a = c by simp [q]]
    exact Equiv.swap_apply_of_ne_of_ne hqbc.symm hcd
  · change Equiv.swap (q b) d (q b) = d
    simp

lemma tableCoordinate_invariant (z : V → C) (c : C × C) (p : colorStabilizer z) :
    Pairing.act p.1 (tableCoordinate z c) = tableCoordinate z c := by
  funext M
  simp only [Pairing.act_apply, tableCoordinate, Pairing.relabel_apply, inv_inv]
  have hi (v : V) : z (p.1⁻¹ v) = z v := (p⁻¹).property v
  simp_rw [hi]
  rw [← Equiv.sum_comp p.1 (fun v => if z v = c.1 ∧ z (M.1 v) = c.2 then (1:ℝ) else 0)]
  apply Finset.sum_congr rfl
  intro v _
  rw [p.property]

lemma mem_candidateEdges (z : V → C) (U : Finset V) (c : C × C) (e : V × V) :
    e ∈ candidateEdges z U c ↔
      e.1 ∉ U ∧ e.2 ∉ U ∧ e.1 ≠ e.2 ∧ z e.1 = c.1 ∧ z e.2 = c.2 := by
  simp [candidateEdges]

lemma candidate_average_eq (z : V → C) (l : List (V × V)) (c : C × C)
    (e f : V × V) (he : e ∈ candidateEdges z (Pairing.edgeSupport l) c)
    (hf : f ∈ candidateEdges z (Pairing.edgeSupport l) c) :
    colorAverage z (Pairing.edgeMonomial (e::l)) =
      colorAverage z (Pairing.edgeMonomial (f::l)) := by
  obtain ⟨ha, hb, hab, hza, hzb⟩ := (mem_candidateEdges _ _ _ _).mp he
  obtain ⟨hc, hd, hcd, hzc, hzd⟩ := (mem_candidateEdges _ _ _ _).mp hf
  obtain ⟨p, hp, hpa, hpb⟩ := exists_color_perm_fixing_pair z (Pairing.edgeSupport l)
    ha hb hc hd hab hcd (hza.trans hzc.symm) (hzb.trans hzd.symm)
  rw [← colorAverage_act z p (Pairing.edgeMonomial (e::l)), Pairing.edgeMonomial_cons]
  have hact : Pairing.act p.1 (Pairing.edgeCoord e * Pairing.edgeMonomial l) =
      Pairing.edgeCoord f * Pairing.edgeMonomial l := by
    rw [Pairing.act_pointwise_mul, Pairing.edgeMonomial_act_fix l p.1 hp,
      Pairing.act_edgeCoord, hpa, hpb]
  rw [hact, Pairing.edgeMonomial_cons]

lemma candidate_sum (z : V → C) (U : Finset V) (c : C × C) (M : Pairing V)
    (hU : ∀ v, M.1 v ∈ U ↔ v ∈ U) :
    ∑ e ∈ candidateEdges z U c, Pairing.edgeCoord e M =
      ∑ v ∈ (Finset.univ \ U), if z v = c.1 ∧ z (M.1 v) = c.2 then (1:ℝ) else 0 := by
  rw [candidateEdges, Finset.sum_filter]
  change (∑ e : V × V, if e.1 ∉ U ∧ e.2 ∉ U ∧ e.1 ≠ e.2 ∧
      z e.1 = c.1 ∧ z e.2 = c.2 then Pairing.edgeCoord e M else 0) = _
  rw [Fintype.sum_prod_type, Finset.sum_sdiff_eq_sub (Finset.subset_univ U)]
  have hpoint (v : V) :
      (∑ w : V, if v ∉ U ∧ w ∉ U ∧ v ≠ w ∧ z v = c.1 ∧ z w = c.2
        then Pairing.edgeCoord (v,w) M else 0) =
      if v ∉ U then (if z v = c.1 ∧ z (M.1 v) = c.2 then 1 else 0) else 0 := by
    rw [Finset.sum_eq_single (M.1 v)]
    · by_cases hv : v ∈ U <;> by_cases ha : z v = c.1 <;>
        by_cases hb : z (M.1 v) = c.2 <;>
        simp [Pairing.edgeCoord, hU v, (M.partner_ne v).symm, hv, ha, hb]
    · intro w _ hw
      simp [Pairing.edgeCoord, Ne.symm hw]
    · simp
  simp_rw [hpoint]
  rw [← Finset.sum_filter]
  have hfilter : Finset.univ.filter (fun v => v ∉ U) = Finset.univ \ U := by ext; simp
  rw [hfilter, Finset.sum_sdiff_eq_sub (Finset.subset_univ U)]

lemma monomial_candidate_identity (z : V → C) (l : List (V × V)) (c : C × C)
    (M₀ : Pairing V) (h₀ : Pairing.ContainsList M₀ l) :
    Pairing.edgeMonomial l * (∑ e ∈ candidateEdges z (Pairing.edgeSupport l) c,
      Pairing.edgeCoord e) =
    Pairing.edgeMonomial l * (tableCoordinate z c -
      (∑ v ∈ Pairing.edgeSupport l,
        if z v = c.1 ∧ z (M₀.1 v) = c.2 then (1:ℝ) else 0) • 1) := by
  funext M
  by_cases hm : Pairing.ContainsList M l
  · simp only [Pi.mul_apply, Pairing.edgeMonomial_eq_indicator, ite_eq_left hm, one_mul,
      Finset.sum_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    rw [candidate_sum z (Pairing.edgeSupport l) c M (fun v => ⟨
      fun hv => by simpa using Pairing.contains_partner_support hm hv,
      fun hv => Pairing.contains_partner_support hm hv⟩)]
    rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ _)]
    unfold tableCoordinate
    congr 1
    apply Finset.sum_congr rfl
    intro v hv
    rw [Pairing.contains_agree_support hm h₀ hv]
  · simp [Pi.mul_apply, Pairing.edgeMonomial_eq_indicator, hm]

end ColorCounting
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.ColorPolynomials ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace MatchingSmoothing
attribute [local instance] Classical.propDecidable
section ColorPolynomials
variable {V : Type u_1} {C : Type u_2} [Fintype V]

lemma colorAverage_recurrence (z : V → C) (l : List (V × V)) (e : V × V)
    (he : e ∈ candidateEdges z (Pairing.edgeSupport l) (z e.1,z e.2))
    (M₀ : Pairing V) (h₀ : Pairing.ContainsList M₀ l) :
    ((candidateEdges z (Pairing.edgeSupport l) (z e.1,z e.2)).card : ℝ) •
      colorAverage z (Pairing.edgeMonomial (e::l)) =
    (tableCoordinate z (z e.1,z e.2) -
      (∑ v ∈ Pairing.edgeSupport l,
        if z v = z e.1 ∧ z (M₀.1 v) = z e.2 then (1:ℝ) else 0) • 1) *
      colorAverage z (Pairing.edgeMonomial l) := by
  let S := candidateEdges z (Pairing.edgeSupport l) (z e.1,z e.2)
  have hsum : (∑ f ∈ S, colorAverage z (Pairing.edgeMonomial (f::l))) =
      ((S.card : ℕ) : ℝ) • colorAverage z (Pairing.edgeMonomial (e::l)) := by
    calc
      _ = ∑ _f ∈ S, colorAverage z (Pairing.edgeMonomial (e::l)) := by
        apply Finset.sum_congr rfl
        intro f hf
        exact candidate_average_eq z l _ f e hf he
      _ = _ := by
        funext M
        simp [Pi.smul_apply]
  have hm : (∑ f ∈ S, Pairing.edgeMonomial (f::l)) =
      Pairing.edgeMonomial l * ∑ f ∈ S, Pairing.edgeCoord f := by
    simp only [Pairing.edgeMonomial_cons, ← Finset.sum_mul, mul_comm]
  rw [← hsum, ← map_sum, hm, monomial_candidate_identity z l _ M₀ h₀, mul_comm]
  apply colorAverage_mul_invariant
  intro p
  rw [map_sub, tableCoordinate_invariant, map_smul]
  rfl

lemma colorAverage_monomial_mem (z : V → C) (l : List (V × V)) :
    colorAverage z (Pairing.edgeMonomial l) ∈ lowDegree (tableCoordinate z) l.length := by
  induction l with
  | nil =>
    simpa only [Pairing.edgeMonomial, List.map_nil, List.prod_nil, colorAverage_one,
      List.length_nil] using one_mem_lowDegree (tableCoordinate z) 0
  | cons e l ih =>
    by_cases hc : ∃ M : Pairing V, Pairing.ContainsList M (e::l)
    · obtain ⟨M₀, hm⟩ := hc
      have h₀ : Pairing.ContainsList M₀ l := fun f hf => hm f (List.mem_cons_of_mem _ hf)
      have hEdge : M₀.1 e.1 = e.2 := hm e (List.mem_cons_self)
      by_cases hv : e.1 ∈ Pairing.edgeSupport l ∨ e.2 ∈ Pairing.edgeSupport l
      · rw [Pairing.redundant_edgeMonomial hEdge h₀ hv]
        exact lowDegree_mono _ (by simp) ih
      · have he : e ∈ candidateEdges z (Pairing.edgeSupport l) (z e.1,z e.2) := by
          apply (mem_candidateEdges _ _ _ _).mpr
          refine ⟨fun h => hv (Or.inl h), fun h => hv (Or.inr h), ?_, rfl, rfl⟩
          intro heq
          exact M₀.partner_ne e.1 (hEdge.trans heq.symm)
        let D := ((candidateEdges z (Pairing.edgeSupport l) (z e.1,z e.2)).card : ℝ)
        have hD : D ≠ 0 := by
          apply Nat.cast_ne_zero.mpr
          exact Finset.card_ne_zero.mpr ⟨e, he⟩
        have hr := colorAverage_recurrence z l e he M₀ h₀
        have hlin : tableCoordinate z (z e.1,z e.2) -
            (∑ v ∈ Pairing.edgeSupport l,
              if z v = z e.1 ∧ z (M₀.1 v) = z e.2 then (1:ℝ) else 0) • 1 ∈
            lowDegree (tableCoordinate z) 1 :=
          (lowDegree (tableCoordinate z) 1).sub_mem (coord_mem_lowDegree _ _)
            ((lowDegree (tableCoordinate z) 1).smul_mem _ (one_mem_lowDegree _ _))
        have hmem := mul_mem_lowDegree (tableCoordinate z) hlin ih
        rw [← hr] at hmem
        change D • colorAverage z (Pairing.edgeMonomial (e::l)) ∈
          lowDegree (tableCoordinate z) (1+l.length) at hmem
        have hh := (lowDegree (tableCoordinate z) (1+l.length)).smul_mem D⁻¹ hmem
        simpa only [smul_smul, inv_mul_cancel₀ hD, one_smul, Nat.add_comm,
          List.length_cons] using hh
    · rw [Pairing.edgeMonomial_zero_of_unsatisfiable _ hc, map_zero]
      exact Submodule.zero_mem _

lemma colorAverage_lowDegree (z : V → C) (d : ℕ)
    (f : Pairing V → ℝ) (hf : f ∈ lowDegree Pairing.edgeCoord d) :
    colorAverage z f ∈ lowDegree (tableCoordinate z) d := by
  apply Submodule.span_induction (p := fun f _ => colorAverage z f ∈
    lowDegree (tableCoordinate z) d) _ _ _ _ hf
  · rintro f ⟨l, hl, rfl⟩
    exact lowDegree_mono _ hl (colorAverage_monomial_mem z l)
  · simp
  · intro f g _ _ hf hg
    simpa only [map_add] using (lowDegree (tableCoordinate z) d).add_mem hf hg
  · intro c f _ hf
    simpa only [map_smul] using (lowDegree (tableCoordinate z) d).smul_mem c hf

end ColorPolynomials

section Substitution
variable {E : Type u_3} {I : Type u_4} {X : Type u_5} {Y : Type u_6}

lemma list_prod_mem_lowDegree (x : E → X → ℝ) (l : List I) (y : I → X → ℝ)
    (hy : ∀ i, y i ∈ lowDegree x 1) : (l.map y).prod ∈ lowDegree x l.length := by
  induction l with
  | nil => exact one_mem_lowDegree x 0
  | cons i l ih =>
    simpa only [List.map_cons, List.prod_cons, List.length_cons, Nat.add_comm] using
      mul_mem_lowDegree x (hy i) ih

lemma lowDegree_substitute (x : E → X → ℝ) (y : I → X → ℝ)
    (hy : ∀ i, y i ∈ lowDegree x 1) (d : ℕ) : lowDegree y d ≤ lowDegree x d := by
  apply Submodule.span_le.mpr
  rintro f ⟨l, hl, rfl⟩
  exact lowDegree_mono x hl (list_prod_mem_lowDegree x l y hy)

lemma lowDegree_lift (x : E → X → ℝ) (d : ℕ) (f : X → ℝ)
    (hf : f ∈ lowDegree x d) :
    ∃ P ∈ lowDegree (fun e (v : E → ℝ) => v e) d,
      ∀ a, f a = P (fun e => x e a) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨l, hl, rfl⟩ := hf
    refine ⟨(l.map (fun e (v : E → ℝ) => v e)).prod,
      Submodule.subset_span ⟨l, hl, rfl⟩, ?_⟩
    intro a
    induction l with
    | nil => rfl
    | cons e l ih =>
      simp only [List.map_cons, List.prod_cons, Pi.mul_apply]
      rw [ih (by simpa only [List.length_cons] using Nat.le_trans (Nat.le_succ _) hl)]
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | add f g _ _ hf hg =>
    obtain ⟨P, hP, hp⟩ := hf
    obtain ⟨Q, hQ, hq⟩ := hg
    exact ⟨P+Q, Submodule.add_mem _ hP hQ, fun a => by simp [hp a, hq a]⟩
  | smul c f _ hf =>
    obtain ⟨P, hP, hp⟩ := hf
    exact ⟨c • P, Submodule.smul_mem _ c hP, fun a => by simp [hp a]⟩

end Substitution
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.TableCoordinates ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_1 u_2 u_3 u_4

namespace MatchingSmoothing
attribute [local instance] Classical.propDecidable
section TableCoordinates
variable {V : Type u_1} {C : Type u_2} [Fintype V]

lemma tableCoordinate_symm (z : V → C) (a b : C) :
    tableCoordinate z (a,b) = tableCoordinate z (b,a) := by
  funext M
  unfold tableCoordinate
  rw [← Equiv.sum_comp M.1 (fun v => if z v = b ∧ z (M.1 v) = a then (1:ℝ) else 0)]
  apply Finset.sum_congr rfl
  intro v _
  simp [M.partner_partner, and_comm]

lemma tableCoordinate_row_sum [Fintype C] (z : V → C) (a : C) :
    ∑ b, tableCoordinate z (a,b) = (histogram z a : ℝ) • 1 := by
  classical
  funext M
  simp only [Finset.sum_apply, tableCoordinate, Pi.smul_apply, Pi.one_apply,
    smul_eq_mul, mul_one]
  rw [Finset.sum_comm, histogram_cast_sum]
  apply Finset.sum_congr rfl
  intro v _
  by_cases ha : z v = a
  · simp [ha]
  · simp [ha]

lemma tableCoordinate_diagonal [Fintype C] (z : V → C) (a : C) :
    tableCoordinate z (a,a) = (histogram z a : ℝ) • 1 -
      ∑ b ∈ Finset.univ.erase a, tableCoordinate z (a,b) := by
  classical
  rw [← tableCoordinate_row_sum]
  rw [eq_sub_iff_add_eq, add_comm]
  exact Finset.sum_erase_add _ _ (Finset.mem_univ a)

end TableCoordinates

section ThreeCoordinates
variable {V : Type u_3} [Fintype V]

lemma tableCoordinate_offdiag_low (z : V → Fin 3) (a b : Fin 3) (hab : a ≠ b) :
    tableCoordinate z (a,b) ∈ lowDegree (crossCoordinate z) 1 := by
  have h01 : tableCoordinate z (0,1) ∈ lowDegree (crossCoordinate z) 1 :=
    coord_mem_lowDegree (crossCoordinate z) 0
  have h02 : tableCoordinate z (0,2) ∈ lowDegree (crossCoordinate z) 1 :=
    coord_mem_lowDegree (crossCoordinate z) 1
  have h12 : tableCoordinate z (1,2) ∈ lowDegree (crossCoordinate z) 1 :=
    coord_mem_lowDegree (crossCoordinate z) 2
  fin_cases a <;> fin_cases b
  all_goals first | exact (hab rfl).elim | exact h01 | exact h02 | exact h12 |
    rwa [tableCoordinate_symm]

lemma tableCoordinate_three_affine (z : V → Fin 3) (c : Fin 3 × Fin 3) :
    tableCoordinate z c ∈ lowDegree (crossCoordinate z) 1 := by
  classical
  obtain ⟨a,b⟩ := c
  by_cases hab : a = b
  · subst b
    rw [tableCoordinate_diagonal]
    apply Submodule.sub_mem
    · exact Submodule.smul_mem _ _ (one_mem_lowDegree _ _)
    · apply Submodule.sum_mem
      intro b hb
      simp only [Finset.mem_erase] at hb
      exact tableCoordinate_offdiag_low z a b hb.1.symm
  · exact tableCoordinate_offdiag_low z a b hab

lemma colorAverage_cross_lowDegree (z : V → Fin 3) (d : ℕ)
    (f : Pairing V → ℝ) (hf : f ∈ lowDegree Pairing.edgeCoord d) :
    colorAverage z f ∈ lowDegree (crossCoordinate z) d :=
  lowDegree_substitute (crossCoordinate z) (tableCoordinate z)
    (tableCoordinate_three_affine z) d (colorAverage_lowDegree z d f hf)

lemma colorAverage_polynomial (z : V → Fin 3) (d : ℕ)
    (f : Pairing V → ℝ) (hf : f ∈ lowDegree Pairing.edgeCoord d) :
    ∃ P ∈ lowDegree (fun i (v : Fin 3 → ℝ) => v i) d,
      ∀ M, colorAverage z f M = P (fun i => crossCoordinate z i M) :=
  lowDegree_lift _ _ _ (colorAverage_cross_lowDegree z d f hf)

end ThreeCoordinates

section TableRelation
variable {H : Type u_4} [Fintype H]

lemma tableCoordinate_relabel (z : H × Bool → Fin 3) (c : Fin 3 × Fin 3)
    (p : Equiv.Perm (H × Bool)) (M : Pairing (H × Bool)) :
    tableCoordinate z c (Pairing.relabel p M) = tableCoordinate (z ∘ p) c M := by
  classical
  unfold tableCoordinate
  apply Fintype.sum_equiv p.symm
  intro v
  split_ifs <;> simp_all [Function.comp_apply, Pairing.relabel_apply]

lemma three_order_indicator (a b x y : Fin 3) :
    (if x=a ∧ y=b then (1:ℝ) else 0) + (if y=a ∧ x=b then (1:ℝ) else 0) =
      (if a=b then 2 else 1) *
      (if threeEdgeType (x,y) = threeEdgeType (a,b) then (1:ℝ) else 0) := by
  fin_cases a <;> fin_cases b <;> fin_cases x <;> fin_cases y <;>
    norm_num [threeEdgeType, Fin.ext_iff]

lemma standard_tableCoordinate (z : H × Bool → Fin 3) (a b : Fin 3) :
    tableCoordinate z (a,b) standardPairing =
      (if a=b then (2:ℝ) else 1) * (threeTable z (threeEdgeType (a,b)) : ℝ) := by
  classical
  simp only [tableCoordinate, Fintype.sum_prod_type, Fintype.sum_bool,
    standardPairing, Equiv.prodCongr_apply]
  change (∑ i, ((if z (i,true)=a ∧ z (i,false)=b then (1:ℝ) else 0) +
    (if z (i,false)=a ∧ z (i,true)=b then (1:ℝ) else 0))) = _
  calc
    _ = ∑ i, (if a=b then (2:ℝ) else 1) *
        (if threeEdgeType (z (i,false),z (i,true)) = threeEdgeType (a,b) then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [add_comm] using three_order_indicator a b (z (i,false)) (z (i,true))
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      exact (histogram_cast_sum (threeEdgeType ∘ pairColorEquiv z) _).symm

lemma tableCoordinate_eq_table [DecidableEq H] (z : H × Bool → Fin 3)
    (M : Pairing (H × Bool)) (a b : Fin 3) :
    tableCoordinate z (a,b) M =
      (if a=b then (2:ℝ) else 1) * (M.table z (threeEdgeType (a,b)) : ℝ) := by
  classical
  obtain ⟨p, rfl⟩ := Pairing.exists_relabel (standardPairing (H := H)) M
  rw [tableCoordinate_relabel, Pairing.table_relabel, standardPairing_table,
    standard_tableCoordinate]

lemma crossCoordinate_eq_table [DecidableEq H] (z : H × Bool → Fin 3)
    (M : Pairing (H × Bool)) (i : Fin 3) :
    crossCoordinate z i M = (M.table z (threeEdgeType (crossPair i)) : ℝ) := by
  rw [crossCoordinate, tableCoordinate_eq_table]
  have hne : (crossPair i).1 ≠ (crossPair i).2 := by fin_cases i <;> decide
  rw [ite_eq_right hne, one_mul]

end TableRelation
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.TablePolynomials ----
namespace OAI

universe u_1 u_2 u_3 u_4

namespace MatchingSmoothing
attribute [local instance] Classical.propDecidable
section PredicateAverage
variable {X : Type u_1} [Fintype X]

lemma predicateAverage_apply (P : X → Prop) (f : X → ℝ) :
    predicateAverage P f = (∑ x, if P x then f x else 0) / Fintype.card {x // P x} := by
  simp only [predicateAverage, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul,
    div_eq_mul_inv]
  rw [mul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : P x <;> simp [hx]

lemma predicateAverage_comp (P : X → Prop) (e : X ≃ X)
    (he : ∀ x, P (e x) ↔ P x) (f : X → ℝ) :
    predicateAverage P (f ∘ e) = predicateAverage P f := by
  rw [predicateAverage_apply, predicateAverage_apply]
  congr 1
  calc
    _ = ∑ x, if P (e x) then f (e x) else 0 := by simp only [he, Function.comp_apply]
    _ = _ := by
      apply Fintype.sum_equiv e
      intro x
      rfl

lemma predicateAverage_of_constant (P : X → Prop) (c : ℝ) (hP : ∃ x, P x)
    (f : X → ℝ) (hf : ∀ x, P x → f x = c) : predicateAverage P f = c := by
  classical
  have : Nonempty {x // P x} := ⟨⟨hP.choose, hP.choose_spec⟩⟩
  rw [predicateAverage_apply]
  have hs : (∑ x, if P x then f x else 0) = Fintype.card {x // P x} * c := by
    calc
      _ = ∑ x ∈ Finset.univ.filter P, f x := (Finset.sum_filter _ _).symm
      _ = ∑ _x ∈ Finset.univ.filter P, c := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hf x (Finset.mem_filter.mp hx).2
      _ = _ := by simp [Fintype.card_subtype]
  rw [hs]
  exact mul_div_cancel_left₀ c (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

end PredicateAverage
end MatchingSmoothing

namespace MatchingSmoothing
attribute [local instance] Classical.propDecidable
section ReynoldsAverage
variable {V : Type u_2} {C : Type u_3} [Fintype V]

lemma predicateAverage_colorAverage (z : V → C) (P : Pairing V → Prop)
    (hP : ∀ (p : colorStabilizer z) M, P (Pairing.relabel p.1 M) ↔ P M)
    (f : Pairing V → ℝ) :
    predicateAverage P (colorAverage z f) = predicateAverage P f := by
  classical
  have hp (p : colorStabilizer z) :
      predicateAverage P (Pairing.act p.1 f) = predicateAverage P f := by
    exact predicateAverage_comp P (Pairing.relabelEquiv p.1⁻¹) (hP p⁻¹) f
  simp only [colorAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearEquiv.coe_coe, map_smul, map_sum]
  simp_rw [hp]
  simp [nsmul_eq_mul, Fintype.card_ne_zero]

end ReynoldsAverage

section TablePolynomial
variable {H : Type u_4} [Fintype H] [DecidableEq H]

lemma table_average_polynomial (z : H × Bool → Fin 3) (d : ℕ)
    (f : Pairing (H × Bool) → ℝ) (hf : f ∈ lowDegree Pairing.edgeCoord d) :
    ∃ P ∈ lowDegree (fun i (v : Fin 3 → ℝ) => v i) d,
      ∀ t : Fin 6 → ℕ, (∃ M : Pairing (H × Bool), M.table z = t) →
        predicateAverage (fun M => M.table z = t) f =
          P (fun i => (t (threeEdgeType (crossPair i)) : ℝ)) := by
  obtain ⟨P, hP, hp⟩ := colorAverage_polynomial z d f hf
  refine ⟨P, hP, ?_⟩
  intro t ht
  have hInv (p : colorStabilizer z) (M : Pairing (H × Bool)) :
      (Pairing.relabel p.1 M).table z = t ↔ M.table z = t := by
    rw [Pairing.table_relabel]
    have hz : z ∘ p.1 = z := funext p.property
    rw [hz]
  rw [← predicateAverage_colorAverage z _ hInv]
  apply predicateAverage_of_constant _ _ ht
  intro M hM
  rw [hp]
  congr 1
  funext i
  rw [crossCoordinate_eq_table, hM]

end TablePolynomial
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.PermutationSmoothing ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

section Averages
variable {X : Type u_1} {Y : Type u_2} [Fintype X] [Fintype Y]
lemma predicateAverage_equiv (e : X ≃ Y) (P : X → Prop) (Q : Y → Prop)
    (he : ∀ x, P x ↔ Q (e x)) (f : Y → ℝ) :
    predicateAverage P (f ∘ e) = predicateAverage Q f := by
  classical
  have hc : Fintype.card {x // P x} = Fintype.card {y // Q y} :=
    Fintype.card_congr (e.subtypeEquiv he)
  rw [predicateAverage_apply, predicateAverage_apply, hc]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun x => by simp only [Function.comp_apply, he])

lemma predicateAverage_eq_expect (P : X → Prop) (f : X → ℝ) :
    predicateAverage P f = 𝔼 x : {x // P x}, f x.1 := by
  rw [predicateAverage_apply, Fintype.expect_eq_sum_div_card]
  congr 1
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype (Finset.univ.filter P) (by simp) f

end Averages

lemma lowProjection_mem (h d : ℕ) (f : Pairing (Vertices h) → ℝ) :
    lowProjection h d f ∈ lowDegree Pairing.edgeCoord d := by
  exact ((polynomialSpace h d).orthogonalProjectionOnto ((matchingEquiv h).symm f)).property

lemma lowProjection_equivariant (h d : ℕ) (p : Equiv.Perm (Vertices h))
    (f : Pairing (Vertices h) → ℝ) :
    lowProjection h d (Pairing.act p f) = Pairing.act p (lowProjection h d f) := by
  have he := starProjection_equivariant (polynomialSpace h d) (relabelIso p)
    (polynomialSpace_invariant p) (by simpa only [relabelIso_symm] using
      (polynomialSpace_invariant (d := d) p⁻¹)) ((matchingEquiv h).symm f)
  exact congrArg (matchingEquiv h) he.symm

lemma predicateAverage_relabel {V : Type u_3} [Fintype V] [DecidableEq V]
    (z : V → Fin 3) (t : Fin 6 → ℕ) (p : Equiv.Perm V) (f : Pairing V → ℝ) :
    predicateAverage (fun M => M.table z = t) (fun M => f (Pairing.relabel p M)) =
      predicateAverage (fun M => M.table (z ∘ p.symm) = t) f := by
  apply predicateAverage_equiv (Pairing.relabelEquiv p)
  intro M
  change M.table z = t ↔ (Pairing.relabel p M).table (z ∘ p.symm) = t
  rw [Pairing.table_relabel]
  have hz : (z ∘ p.symm) ∘ p = z := by funext a; simp
  rw [hz]

lemma expect_perm_colorings {V : Type u_4} {C : Type u_5} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C] (z : V → C) (φ : (V → C) → ℝ) :
    (𝔼 p : Equiv.Perm V, φ (z ∘ p)) =
      𝔼 w : Colorings V C (histogram z), φ w.1 := by
  have : Nonempty (Colorings V C (histogram z)) := ⟨⟨z,rfl⟩⟩
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  apply (div_eq_div_iff (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)).mpr
  simpa only [mul_comm] using mean_perm_comp z φ

lemma fiberAverage_eq_predicateAverage {X : Type u_7} {Z : Type u_8} [Fintype X] [Fintype Z]
    (P : X → Z → Prop) (f : X → ℝ) (z : Z) :
    fiberAverage P f z = predicateAverage (fun x => P x z) f := by
  simp only [fiberAverage, conditionalAverage, incidence, predicateAverage_apply,
    ite_mul, one_mul, zero_mul]

lemma fiberEnergy_eq {h : ℕ} (f₀ : Vertices h → Fin 3)
    (f : Pairing (Vertices h) → ℝ) :
    (∑ z, fiberAverage (tableRelation f₀) f z ^ 2) /
      Fintype.card (Colorings (Vertices h) (Fin 3) (histogram f₀)) =
    tableEnergy (histogram f₀) (threeTable f₀) f := by
  simp_rw [fiberAverage_eq_predicateAverage]
  rw [tableEnergy, Fintype.expect_eq_sum_div_card]
  rfl

lemma permutation_energy_eq {V : Type u_9} [Fintype V] [DecidableEq V]
    (z : V → Fin 3) (t : Fin 6 → ℕ) (f : Pairing V → ℝ) :
    (𝔼 p : Equiv.Perm V, (predicateAverage (fun M => M.table z = t)
      (fun M => f (Pairing.relabel p M)))^2) = tableEnergy (histogram z) t f := by
  simp_rw [predicateAverage_relabel]
  calc
    _ = 𝔼 p : Equiv.Perm V,
        (predicateAverage (fun M => M.table (z ∘ p) = t) f)^2 := by
      apply Fintype.expect_equiv (Equiv.inv (Equiv.Perm V))
      intro p
      rfl
    _ = _ := expect_perm_colorings z (fun w =>
      (predicateAverage (fun M => M.table w = t) f)^2)

lemma uniform_permutation_smoothing (K : ℕ) :
    ∃ d H : ℕ, 0 < d ∧ ∀ h : ℕ, H ≤ h →
      ∀ (z : Vertices h → Fin 3), (∀ i, 0 < histogram z i) →
      ∀ (M₀ : Pairing (Vertices h)) (f : Pairing (Vertices h) → ℝ),
      (𝔼 p : Equiv.Perm (Vertices h),
        (predicateAverage (fun M => M.table z = M₀.table z)
          (fun M => (f - lowProjection h d f) (Pairing.relabel p M)))^2) ≤
      ((2*h : ℝ)^(2*K))⁻¹ * (𝔼 M, (f M)^2) := by
  obtain ⟨d,H,hd,hbound⟩ := uniform_table_smoothing K
  refine ⟨d,H,hd,?_⟩
  intro h hh z hz M₀ f
  obtain ⟨p₀, hp₀⟩ := Pairing.exists_relabel (standardPairing (H := Fin h)) M₀
  let f₀ := z ∘ p₀
  have hhist : histogram f₀ = histogram z := histogram_comp_perm z p₀
  have ht : threeTable f₀ = M₀.table z := by
    rw [← hp₀, Pairing.table_relabel, standardPairing_table]
  have hb := hbound h hh f₀ (by simpa only [hhist] using hz) ((matchingEquiv h).symm f)
  have heg : matchingEquiv h ((matchingEquiv h).symm f -
      polynomialProjection h d ((matchingEquiv h).symm f)) = f - lowProjection h d f := by
    simp only [map_sub, LinearEquiv.apply_symm_apply]
    rfl
  rw [fiberEnergy_eq, heg, ht, hhist] at hb
  rw [permutation_energy_eq, Fintype.expect_eq_sum_div_card]
  exact hb

end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.CommonSelection ----
namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing
open scoped BigOperators

section GroupAveraging
variable {G : Type u_1} {I : Type u_2} [Fintype G] [Group G] [Fintype I]
  {P : I → Type u_3} [∀ i, Fintype (P i)] [∀ i, Nonempty (P i)]

lemma mean_right_translate (g : G) (f : G → ℝ) :
    (𝔼 a : G, f (a*g)) = 𝔼 a : G, f a := by
  exact Fintype.expect_equiv (Equiv.mulRight g) _ _ (fun _ => rfl)

omit [Fintype I] in
lemma mean_le_of_local_means (lift : (i : I) → P i → G)
    (err : I → G → ℝ) (b : I → ℝ)
    (hb : ∀ i a, (𝔼 p : P i, err i (a * lift i p)) ≤ b i) (i : I) :
    (𝔼 a : G, err i a) ≤ b i := by
  have hh : (𝔼 a : G, 𝔼 p : P i, err i (a * lift i p)) ≤ b i :=
    Finset.expect_le Finset.univ_nonempty (fun a _ => hb i a)
  rw [Finset.expect_comm] at hh
  simpa only [mean_right_translate, Fintype.expect_const] using hh

lemma exists_total_le_of_local_means (lift : (i : I) → P i → G)
    (err : I → G → ℝ) (b : I → ℝ)
    (hb : ∀ i a, (𝔼 p : P i, err i (a * lift i p)) ≤ b i) :
    ∃ a : G, (∑ i, err i a) ≤ ∑ i, b i := by
  have he (i : I) : (𝔼 a : G, err i a) ≤ b i :=
    mean_le_of_local_means lift err b hb i
  have htotal : (𝔼 a : G, ∑ i, err i a) ≤ ∑ i, b i := by
    rw [Finset.expect_sum_comm]
    exact Finset.sum_le_sum (fun i _ => he i)
  obtain ⟨a, _, ha⟩ := Finset.exists_le_of_expect_le Finset.univ_nonempty htotal
  exact ⟨a,ha⟩

end GroupAveraging
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.SimultaneousSmoothing ----
namespace OAI

namespace MatchingSmoothing
open scoped BigOperators

lemma lowProjection_comp (h d : ℕ) (p : Equiv.Perm (Vertices h))
    (f : Pairing (Vertices h) → ℝ) :
    lowProjection h d (fun M => f (Pairing.relabel p M)) =
      fun M => lowProjection h d f (Pairing.relabel p M) := by
  have he := lowProjection_equivariant h d p⁻¹ f
  have hc (f : Pairing (Vertices h) → ℝ) :
      Pairing.act p⁻¹ f = fun M => f (Pairing.relabel p M) := by
    ext M
    simp only [Pairing.act_apply, inv_inv]
  rw [hc, hc] at he
  exact he

lemma simultaneous_table_approximation (K : ℕ) :
    ∃ d H : ℕ, 0 < d ∧ ∀ h : ℕ, H ≤ h →
      ∀ (G I T : Type) [Fintype G] [Group G] [Fintype I] [Fintype T]
      (z : I → Vertices h → Fin 3), (∀ i c, 0 < histogram (z i) c) →
      ∀ (M : I → T → Pairing (Vertices h))
      (lift : I → Equiv.Perm (Vertices h) → G)
      (g : I → G → Pairing (Vertices h) → ℝ),
      (∀ i a p, g i (a * lift i p) = fun N => g i a (Pairing.relabel p N)) →
      ∀ B : ℝ, (∀ i a N, (g i a N)^2 ≤ B^2) →
      ∃ a : G, ∃ P : I → (Fin 3 → ℝ) → ℝ,
        (∀ i, P i ∈ lowDegree (fun c (v : Fin 3 → ℝ) => v c) d) ∧
        (∑ i, ∑ t : T,
          (predicateAverage (fun N => N.table (z i) = (M i t).table (z i)) (g i a) -
            P i (fun c => ((M i t).table (z i) (threeEdgeType (crossPair c)) : ℝ)))^2)
          ≤ (Fintype.card I : ℝ) * Fintype.card T * ((2*h : ℝ)^(2*K))⁻¹ * B^2 := by
  classical
  obtain ⟨d,H,hd,hsm⟩ := uniform_permutation_smoothing K
  refine ⟨d,H,hd,?_⟩
  intro h hh G I T _ _ _ _ z hz M lift g hcov B hB
  let : Nonempty (Pairing (Vertices h)) := ⟨standardPairing⟩
  let err : I → G → ℝ := fun i a => ∑ t : T,
    (predicateAverage (fun N => N.table (z i) = (M i t).table (z i))
      (g i a - lowProjection h d (g i a)))^2
  let b : ℝ := (Fintype.card T : ℝ) * ((2*h : ℝ)^(2*K))⁻¹ * B^2
  have hlocal (i : I) (a : G) : (𝔼 p : Equiv.Perm (Vertices h), err i (a*lift i p)) ≤ b := by
    have hres (p : Equiv.Perm (Vertices h)) :
        g i (a*lift i p) - lowProjection h d (g i (a*lift i p)) =
          fun N => (g i a - lowProjection h d (g i a)) (Pairing.relabel p N) := by
      rw [hcov, lowProjection_comp]
      rfl
    simp only [err, hres]
    rw [Finset.expect_sum_comm]
    have hmean : (𝔼 N : Pairing (Vertices h), (g i a N)^2) ≤ B^2 :=
      Finset.expect_le Finset.univ_nonempty (fun N _ => hB i a N)
    calc
      _ ≤ ∑ _t : T, ((2*h : ℝ)^(2*K))⁻¹ * B^2 := by
        apply Finset.sum_le_sum
        intro t _
        exact (hsm h hh (z i) (hz i) (M i t) (g i a)).trans
          (mul_le_mul_of_nonneg_left hmean (by positivity))
      _ = b := by simp [b, mul_assoc]
  obtain ⟨a,ha⟩ := exists_total_le_of_local_means lift err (fun _ => b) hlocal
  have hex (i : I) := table_average_polynomial (z i) d (lowProjection h d (g i a))
    (lowProjection_mem h d (g i a))
  choose P hP he using hex
  refine ⟨a,P,hP,?_⟩
  have ht (i : I) (t : T) := he i ((M i t).table (z i)) ⟨M i t, rfl⟩
  simp only [err, map_sub, ht, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at ha
  simpa only [b, mul_assoc] using ha

end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.MatchingFibers ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10

namespace MatchingSmoothing
namespace Pairing
variable {A : Type u_1} {B : Type u_2} {C : Type u_3}

lemma transport_perm (p : Equiv.Perm A) (M : Pairing A) : transport p M = relabel p M := rfl

lemma sum_relabel_left (p : Equiv.Perm A) (M : Pairing A) (N : Pairing B) :
    sum (relabel p M) N = relabel (Equiv.sumCongr p (Equiv.refl B)) (sum M N) := by
  ext v
  cases v <;> rfl

lemma transport_relabel (e : A ≃ B) (p : Equiv.Perm A) (M : Pairing A) :
    transport e (relabel p M) = relabel (e.symm.trans (p.trans e)) (transport e M) := by
  ext b
  simp only [transport_apply, relabel_apply, Equiv.Perm.inv_def,
    Equiv.symm_trans_apply, Equiv.trans_apply, Equiv.symm_symm,
    Equiv.symm_apply_apply]

end Pairing

section Coordinates
variable {A : Type u_6} {B : Type u_7} {C : Type u_8} [Fintype A] [Fintype B]
attribute [local instance] Classical.propDecidable

lemma tableCoordinate_transport (e : A ≃ B) (z : B → C) (c : C × C) (M : Pairing A) :
    tableCoordinate z c (Pairing.transport e M) = tableCoordinate (z ∘ e) c M := by
  unfold tableCoordinate
  rw [← e.sum_comp (fun b => if z b = c.1 ∧ z ((Pairing.transport e M).1 b) = c.2 then (1:ℝ) else 0)]
  simp only [Pairing.transport_apply, Equiv.symm_apply_apply, Function.comp_apply]

end Coordinates
end MatchingSmoothing

namespace MatchingSmoothing.Pairing
variable {A : Type u_9} {B : Type u_10}

end MatchingSmoothing.Pairing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.GlobalGeometry ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

section ThreeCellGeometry
variable {A : Type u_1} {B : Type u_2} {C : Type u_3} [Fintype A] [Fintype B] [Fintype C]

end ThreeCellGeometry

section GlobalExtension
variable {D : Type u_5} {C : Type u_6} {I : Type u_7} [DecidableEq I]

lemma extendLocal_relabel (i : I) (p : Equiv.Perm (D ⊕ C))
    (M : Pairing (D ⊕ C)) (N : {j : I // j ≠ i} → Pairing C) :
    extendLocal i (Pairing.relabel p M) N = Pairing.relabel (liftLocal i p) (extendLocal i M N) := by
  rw [extendLocal, Pairing.sum_relabel_left, Pairing.transport_relabel]
  rfl

lemma extendLocal_sum (i : I) (M : Pairing D) (N : I → Pairing C) :
    extendLocal i (Pairing.sum M (N i)) (fun j => N j.1) =
      Pairing.sum M (Pairing.cellwise N) := by
  apply Pairing.ext
  intro v
  obtain ⟨v,rfl⟩ := (localSplitEquiv (D := D) (C := C) i).surjective v
  simp only [extendLocal, Pairing.transport_apply, Equiv.symm_apply_apply]
  cases v with
  | inl v =>
    cases v with
    | inl d => rfl
    | inr c => rfl
  | inr jc => rfl

end GlobalExtension
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.AdmissibleTables ----
namespace OAI

universe u_1 u_2 u_3 u_4

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

section ColorTransport
variable {A : Type u_1} {B : Type u_2} {C : Type u_3} [Fintype A] [Fintype B] [Fintype C] [DecidableEq C]
omit [Fintype C] in
lemma colorEquiv_spec (f : A → C) (g : B → C) (h : histogram f = histogram g) (a : A) :
    g (colorEquiv f g h a) = f a := by
  exact (Fintype.equivOfCardEq (congrFun h (f a)) ⟨a,rfl⟩).property
end ColorTransport

lemma edgeColor_histogram (E : Fin 6 → ℕ) : histogram (edgeColor E) = endpointSizes E := by
  funext c
  apply Nat.cast_injective (R := ℝ)
  rw [histogram_cast_sum]
  simp only [Fintype.sum_prod_type, Fintype.sum_sigma, Fintype.sum_bool]
  fin_cases c <;> simp [edgeColor, endpointSizes, typePair, Fin.sum_univ_succ] <;> ring

lemma edgeColor_cross (E : Fin 6 → ℕ) (i : Fin 3) :
    crossCoordinate (edgeColor E) i (standardPairing (H := TypedEdges E)) =
      (![E 1,E 2,E 4] i : ℝ) := by
  simp only [crossCoordinate, tableCoordinate, Fintype.sum_prod_type,
    Fintype.sum_sigma, Fintype.sum_bool]
  fin_cases i <;> simp [crossPair, standardPairing, edgeColor, typePair, Fin.sum_univ_succ]

lemma exists_pairing_of_endpoints {V : Type u_4} [Fintype V]
    (z : V → Fin 3) (E : Fin 6 → ℕ) (hz : histogram z = endpointSizes E) :
    ∃ M : Pairing V, ∀ i : Fin 3, crossCoordinate z i M = (![E 1,E 2,E 4] i : ℝ) := by
  let e := colorEquiv (edgeColor E) z ((edgeColor_histogram E).trans hz.symm)
  have he : z ∘ e = edgeColor E := funext (colorEquiv_spec _ _ _)
  refine ⟨Pairing.transport e standardPairing, ?_⟩
  intro i
  rw [crossCoordinate, tableCoordinate_transport, he]
  exact edgeColor_cross E i

lemma tripleColor_histogram (s : ℕ) :
    histogram (@tripleColor s) = ![2*s+1,2*s+1,2*s] := by
  funext c
  apply Nat.cast_injective (R := ℝ)
  rw [histogram_cast_sum]
  fin_cases c <;> simp [tripleColor, Fintype.sum_sum_type, Nat.cast_add, Nat.cast_mul]; ring

lemma triple_histogram_pos {s : ℕ} (hs : 0 < s) (i : Fin 3) :
    0 < histogram (@tripleColor s) i := by
  rw [tripleColor_histogram]
  fin_cases i <;> simp; omega

end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.TableGeometry ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma coordinates_eq_of_cross_eq {V : Type u_3} [Fintype V]
    (z : V → Fin 3) (M N : Pairing V)
    (h : crossVector z M = crossVector z N) : ∀ a b, tableCoordinate z (a,b) M = tableCoordinate z (a,b) N := by
  have hb (a b : Fin 3) (hab : a ≠ b) : tableCoordinate z (a,b) M = tableCoordinate z (a,b) N := by
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    fin_cases a <;> fin_cases b
    all_goals first | exact (hab rfl).elim | exact h0 | exact h1 | exact h2 |
      rwa [tableCoordinate_symm]
  intro a b
  by_cases hab : a = b
  · subst b
    rw [tableCoordinate_diagonal]
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one,
      Finset.sum_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro b hb'
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hb'
    exact hb a b hb'.symm
  · exact hb a b hab

lemma table_eq_iff_cross {H : Type u_4} [Fintype H] [DecidableEq H]
    (z : H × Bool → Fin 3) (M N : Pairing (H × Bool)) :
    M.table z = N.table z ↔ crossVector z M = crossVector z N := by
  constructor
  · intro h
    funext i
    simp only [crossVector, crossCoordinate_eq_table, h]
  · intro h
    have hh := coordinates_eq_of_cross_eq z M N h
    have get (a b : Fin 3) : M.table z (threeEdgeType (a,b)) = N.table z (threeEdgeType (a,b)) := by
      have he := hh a b
      rw [tableCoordinate_eq_table, tableCoordinate_eq_table] at he
      split_ifs at he <;> exact_mod_cast (by linarith : (M.table z (threeEdgeType (a,b)) : ℝ) = N.table z (threeEdgeType (a,b)))
    funext i
    fin_cases i
    · exact get 0 0
    · exact get 0 1
    · exact get 0 2
    · exact get 1 1
    · exact get 1 2
    · exact get 2 2

lemma crossVector_transport {V : Type u_5} {W : Type u_6} [Fintype V] [Fintype W]
    (e : V ≃ W) (z : W → Fin 3) (M : Pairing V) :
    crossVector z (Pairing.transport e M) = crossVector (z ∘ e) M := by
  funext i
  exact tableCoordinate_transport e z (crossPair i) M

lemma histogram_comp_equiv {V : Type u_7} {W : Type u_8} {C : Type u_9} [Fintype V] [Fintype W] [DecidableEq C]
    (z : W → C) (e : V ≃ W) : histogram (z ∘ e) = histogram z := by
  funext c
  apply Fintype.card_congr
  exact e.subtypeEquiv (fun _ => Iff.rfl)

end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.CrossSelection ----
namespace OAI

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma simultaneous_cross_approximation (K : ℕ) :
    ∃ d H : ℕ, 0 < d ∧ ∀ h : ℕ, H ≤ h →
      ∀ (V G I T : Type) [Fintype V] [Fintype G] [Group G] [Fintype I] [Fintype T]
      (_e : V ≃ Vertices h) (z : I → V → Fin 3), (∀ i c, 0 < histogram (z i) c) →
      ∀ (M : I → T → Pairing V)
      (lift : I → Equiv.Perm V → G)
      (g : I → G → Pairing V → ℝ),
      (∀ i a p, g i (a * lift i p) = fun N => g i a (Pairing.relabel p N)) →
      ∀ B : ℝ, (∀ i a N, (g i a N)^2 ≤ B^2) →
      ∃ a : G, ∃ P : I → (Fin 3 → ℝ) → ℝ,
        (∀ i, P i ∈ lowDegree (fun c (v : Fin 3 → ℝ) => v c) d) ∧
        (∑ i, ∑ t : T,
          (predicateAverage (fun N => crossVector (z i) N = crossVector (z i) (M i t)) (g i a) -
            P i (crossVector (z i) (M i t)))^2)
          ≤ (Fintype.card I : ℝ) * Fintype.card T * ((2*h : ℝ)^(2*K))⁻¹ * B^2 := by
  classical
  obtain ⟨d,H,hd,hmain⟩ := simultaneous_table_approximation K
  refine ⟨d,H,hd,?_⟩
  intro h hh V G I T _ _ _ _ _ e z hz M lift g hcov B hB
  let ev := Pairing.transportEquiv e.symm
  let z' := fun i => z i ∘ e.symm
  let M' := fun i t => Pairing.transport e (M i t)
  let lift' := fun i (p : Equiv.Perm (Vertices h)) => lift i (e.trans (p.trans e.symm))
  let g' := fun i a N => g i a (ev N)
  have hc (i : I) (a : G) (p : Equiv.Perm (Vertices h)) :
      g' i (a * lift' i p) = fun N => g' i a (Pairing.relabel p N) := by
    funext N
    change g i (a * lift' i p) (ev N) = _
    rw [hcov]
    change g i a (Pairing.relabel (e.trans (p.trans e.symm)) (Pairing.transport e.symm N)) =
      g i a (Pairing.transport e.symm (Pairing.relabel p N))
    rw [Pairing.transport_relabel]
    rfl
  obtain ⟨a,P,hP,hbound⟩ := hmain h hh G I T z'
    (fun i c => by
      have he : histogram (z' i) = histogram (z i) := histogram_comp_equiv (z i) e.symm
      rw [he]
      exact hz i c)
    M' lift' g' hc B (fun i a N => hB i a (ev N))
  refine ⟨a,P,hP,?_⟩
  have hvec (i : I) (t : T) : crossVector (z' i) (M' i t) = crossVector (z i) (M i t) := by
    rw [crossVector_transport]
    have he : z' i ∘ e = z i := by funext v; simp [z']
    rw [he]
  have hav (i : I) (t : T) :
      predicateAverage (fun N => N.table (z' i) = (M' i t).table (z' i)) (g' i a) =
        predicateAverage (fun N => crossVector (z i) N = crossVector (z i) (M i t)) (g i a) := by
    apply predicateAverage_equiv ev
    intro N
    rw [table_eq_iff_cross, hvec]
    change _ ↔ crossVector (z i) (Pairing.transport e.symm N) = _
    rw [crossVector_transport]
  have htvec (i : I) (t : T) :
      (fun c => ((M' i t).table (z' i) (threeEdgeType (crossPair c)) : ℝ)) =
        crossVector (z i) (M i t) := by
    rw [← hvec]
    funext c
    exact (crossCoordinate_eq_table _ _ _).symm
  simpa only [hav, htvec] using hbound

end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.AdmissiblePoints ----
namespace OAI

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma triple_pairing_five {s : ℕ} (hs : 1 ≤ s) (j : Fin 5) :
    ∃ M : Pairing (TripleVertices s), crossVector tripleColor M =
      (![![1,0,0], ![0,1,1], ![3,0,0], ![1,2,0], ![1,0,2]] j : Fin 3 → ℝ) := by
  have hex (E : Fin 6 → ℕ) (he : endpointSizes E = ![2*s+1,2*s+1,2*s]) :
      ∃ M : Pairing (TripleVertices s), crossVector tripleColor M =
        (fun i => (![E 1,E 2,E 4] i : ℝ)) := by
    obtain ⟨M,hM⟩ := exists_pairing_of_endpoints tripleColor E (by rw [tripleColor_histogram, he])
    exact ⟨M,funext hM⟩
  fin_cases j
  · obtain ⟨M,hM⟩ := hex ![s,1,0,s,0,s] (by ext i; fin_cases i <;> simp [endpointSizes]; omega)
    exact ⟨M,by rw [hM]; ext i; fin_cases i <;> simp⟩
  · obtain ⟨M,hM⟩ := hex ![s,0,1,s,1,s-1] (by ext i; fin_cases i <;> simp [endpointSizes]; omega)
    exact ⟨M,by rw [hM]; ext i; fin_cases i <;> simp⟩
  · obtain ⟨M,hM⟩ := hex ![s-1,3,0,s-1,0,s] (by ext i; fin_cases i <;> simp [endpointSizes] <;> omega)
    exact ⟨M,by rw [hM]; ext i; fin_cases i <;> simp⟩
  · obtain ⟨M,hM⟩ := hex ![s-1,1,2,s,0,s-1] (by ext i; fin_cases i <;> simp [endpointSizes] <;> omega)
    exact ⟨M,by rw [hM]; ext i; fin_cases i <;> simp⟩
  · obtain ⟨M,hM⟩ := hex ![s,1,0,s-1,2,s-1] (by ext i; fin_cases i <;> simp [endpointSizes] <;> omega)
    exact ⟨M,by rw [hM]; ext i; fin_cases i <;> simp⟩

lemma triple_pairing_grid {s l d : ℕ} (hs : 2*l*d ≤ s) (k : Fin 3 → Fin (d+1)) :
    ∃ M : Pairing (TripleVertices s), crossVector tripleColor M =
      (fun a => (![1,0,0] a : ℝ) + (2*l:ℝ)*(k a:ℝ)) := by
  let E : Fin 6 → ℕ := ![s-l*((k 0:ℕ)+k 1), 1+2*l*k 0, 2*l*k 1,
    s-l*((k 0:ℕ)+k 2), 2*l*k 2, s-l*((k 1:ℕ)+k 2)]
  have hk (a : Fin 3) : (k a : ℕ) ≤ d := Nat.le_of_lt_succ (k a).isLt
  have hle (a b : Fin 3) : l*((k a:ℕ)+k b) ≤ s := by
    calc
      _ ≤ l*(d+d) := Nat.mul_le_mul_left l (Nat.add_le_add (hk a) (hk b))
      _ = 2*l*d := by ring
      _ ≤ s := hs
  have he : endpointSizes E = ![2*s+1,2*s+1,2*s] := by
    ext i
    fin_cases i <;> simp [endpointSizes, E]
    · have h := Nat.sub_add_cancel (hle 0 1); nlinarith
    · have h := Nat.sub_add_cancel (hle 0 2); nlinarith
    · have h := Nat.sub_add_cancel (hle 1 2); nlinarith
  obtain ⟨M,hM⟩ := exists_pairing_of_endpoints tripleColor E (by rw [tripleColor_histogram, he])
  refine ⟨M,?_⟩
  funext i
  rw [crossVector, hM]
  fin_cases i <;> simp [E, Nat.cast_add, Nat.cast_mul]

end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.CutGeometry ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma tableCoordinate_localcut {V : Type u_5} [Fintype V] (z : V → Fin 3)
    (M : Pairing V) (b : Bool) :
    tableCoordinate (localCutColor b ∘ z) (true,false) M =
      crossVector z M 0 + crossVector z M (if b then 2 else 1) := by
  cases b
  · change _ = tableCoordinate z (0,1) M + tableCoordinate z (0,2) M
    simp only [tableCoordinate, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    rcases (show z v=0 ∨ z v=1 ∨ z v=2 by omega) with hv | hv | hv <;>
      rcases (show z (M.1 v)=0 ∨ z (M.1 v)=1 ∨ z (M.1 v)=2 by omega) with hw | hw | hw <;>
      simp [Function.comp_apply, hv, hw, localCutColor]
  · change _ = tableCoordinate z (0,1) M + tableCoordinate z (1,2) M
    rw [tableCoordinate_symm z 1 2]
    simp only [tableCoordinate, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    rcases (show z v=0 ∨ z v=1 ∨ z v=2 by omega) with hv | hv | hv <;>
      rcases (show z (M.1 v)=0 ∨ z (M.1 v)=1 ∨ z (M.1 v)=2 by omega) with hw | hw | hw <;>
      simp [Function.comp_apply, hv, hw, localCutColor]

lemma tableCoordinate_cellwise_cut {I : Type u_6} {C : Type u_7} [Fintype I] [Fintype C]
    (y : I → Bool) (N : I → Pairing C) :
    tableCoordinate (fun v : I × C => y v.1) (true,false) (Pairing.cellwise N) = 0 := by
  apply (tableCoordinate_eq_zero_iff _ _ _).mpr
  rintro ⟨j,c⟩ ⟨h1,h2⟩
  have he : (true : Bool) = false := h1.symm.trans h2
  cases he

lemma localSplit_cut {A : Type u_8} {B : Type u_9} {C : Type u_10} {I : Type u_11} [DecidableEq I]
    (y : I → Bool) (i : I) :
    globalCutColor (A := A) (B := B) (C := C) y ∘ localSplitEquiv i =
      Sum.elim (localCutColor (y i) ∘ threeColor)
        (fun v : {j : I // j ≠ i} × C => y v.1.1) := by
  funext v
  rcases v with (a | c) | ⟨j,c⟩
  · cases a <;> rfl
  · rfl
  · rfl

lemma extendLocal_cut {A : Type u_12} {B : Type u_13} {C : Type u_14} {I : Type u_15} [Fintype A] [Fintype B] [Fintype C]
    [Fintype I] [DecidableEq I] (y : I → Bool) (i : I)
    (M : Pairing ((A ⊕ B) ⊕ C)) (N : {j : I // j ≠ i} → Pairing C) :
    tableCoordinate (globalCutColor y) (true,false) (extendLocal i M N) =
      crossVector threeColor M 0 + crossVector threeColor M (if y i then 2 else 1) := by
  rw [extendLocal, tableCoordinate_transport, localSplit_cut, tableCoordinate_sum,
    tableCoordinate_cellwise_cut (fun j : {j : I // j ≠ i} => y j.1),
    add_zero, tableCoordinate_localcut]

lemma globalCutColor_card (s q : ℕ) (y : Fin q → Bool) :
    Fintype.card {v : GlobalVertices s q // globalCutColor y v = true} =
      2*s+1 + Fintype.card {i : Fin q // y i = true} * (2*s) := by
  classical
  have hc (V : Type) [Fintype V] (f : V → Bool) :
      Fintype.card {v // f v = true} = histogram f true := by
    simp only [Fintype.card_subtype, histogram]
  rw [hc, hc]
  apply Nat.cast_injective (R := ℝ)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    histogram_cast_sum]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, globalCutColor,
    Sum.elim_inl, Sum.elim_inr, Fintype.sum_bool, ite_true, Bool.false_eq_true,
    ite_false, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, mul_zero, add_zero, Finset.sum_add_distrib, Finset.sum_mul,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : y i = true <;> simp [h]
  ring

lemma globalCutColor_odd (s q : ℕ) (y : Fin q → Bool) :
    Odd (Fintype.card {v : GlobalVertices s q // globalCutColor y v = true}) := by
  rw [globalCutColor_card]
  exact ⟨s+Fintype.card {i : Fin q // y i = true}*s, by ring⟩

lemma globalVertices_card (s q : ℕ) :
    Fintype.card (GlobalVertices s q) = 2*s*(q+2)+2 := by
  simp only [GlobalVertices, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool]
  ring

end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.CellAverages ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable
section CellAverages
variable {A : Type u_1} {B : Type u_2} {C : Type u_3} {I : Type u_4} [Fintype A] [Fintype B] [Fintype C] [Fintype I] [DecidableEq I]

omit [Fintype A] [Fintype B] in
lemma extensionAverage_relabel (i : I) (p : Equiv.Perm ((A ⊕ B) ⊕ C))
    (f : Pairing ((A ⊕ B) ⊕ (I × C)) → ℝ) (M : Pairing ((A ⊕ B) ⊕ C)) :
    extensionAverage i f (Pairing.relabel p M) =
      extensionAverage i (fun N => f (Pairing.relabel (liftLocal i p) N)) M := by
  simp only [extensionAverage, extendLocal_relabel]

lemma expect_pair_product {X : Type u_5} {Y : Type u_6} [Fintype X] [Fintype Y] (f : X × Y → ℝ) :
    (𝔼 p : X × Y, f p) = 𝔼 x : X, 𝔼 y : Y, f (x,y) := by
  rw [← Finset.univ_product_univ, Finset.expect_product]

lemma cellAverage_star (i : I) (f : Pairing ((A ⊕ B) ⊕ (I × C)) → ℝ) (x : ℝ) :
    cellAverage i f ![x,0,0] =
      𝔼 M : {M : Pairing (A ⊕ B) // tableCoordinate abColor (0,1) M = x},
        𝔼 N : I → Pairing C, f (Pairing.sum M.1 (Pairing.cellwise N)) := by
  classical
  rw [cellAverage, predicateAverage_eq_expect]
  have he := Fintype.expect_equiv (starFiberEquiv (A := A) (B := B) (C := C) x)
    (fun p => extensionAverage i f (Pairing.sum p.1.1 p.2))
    (fun p => extensionAverage i f p.1) (fun _ => rfl)
  calc
    _ = 𝔼 p : {M : Pairing (A ⊕ B) // tableCoordinate abColor (0,1) M = x} × Pairing C,
        extensionAverage i f (Pairing.sum p.1.1 p.2) := by
          convert he.symm using 1
          congr 1
          ext; simp
    _ = _ := ?_
  rw [expect_pair_product]
  apply Finset.expect_congr rfl
  intro M _
  simp only [extensionAverage]
  calc
    _ = 𝔼 p : Pairing C × ({j : I // j ≠ i} → Pairing C),
        f (extendLocal i (Pairing.sum M.1 p.1) p.2) := by
      convert (expect_pair_product (fun p : Pairing C × ({j : I // j ≠ i} → Pairing C) =>
        f (extendLocal i (Pairing.sum M.1 p.1) p.2))).symm using 1
    _ = _ := (Fintype.expect_equiv (Equiv.piSplitAt i (fun _ : I => Pairing C))
      (fun N => f (Pairing.sum M.1 (Pairing.cellwise N)))
      (fun p => f (extendLocal i (Pairing.sum M.1 p.1) p.2))
      (fun N => by rw [Equiv.piSplitAt_apply, extendLocal_sum])).symm

lemma cellAverage_const (i : I) (f : Pairing ((A ⊕ B) ⊕ (I × C)) → ℝ)
    (x : Fin 3 → ℝ) (c : ℝ) (hM : ∃ M : Pairing ((A ⊕ B) ⊕ C), crossVector threeColor M = x)
    [Nonempty (Pairing C)]
    (hf : ∀ M, crossVector threeColor M = x → ∀ N, f (extendLocal i M N) = c) :
    cellAverage i f x = c := by
  apply predicateAverage_of_constant _ _ hM
  intro M hM
  simp only [extensionAverage, hf M hM, Finset.expect_const, Finset.univ_nonempty]

end CellAverages
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.DeterminantNormalization ----
namespace OAI

universe u_1 u_2 u_3

namespace PerfectMatchingPSD
open Matrix Set
variable {R : Type u_1} {I : Type u_2} {J : Type u_3} [Fintype R] [DecidableEq R]

omit [Fintype R] [DecidableEq R] in
lemma convex_posSemidef : Convex ℝ {A : Matrix R R ℝ | A.PosSemidef} := by
  intro A hA B hB a b ha hb _
  exact (hA.smul ha).add (hB.smul hb)

lemma hasDerivAt_det_one_add (A : Matrix R R ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t • A).det) A.trace 0 := by
  let p : Polynomial ℝ := (1 + (Polynomial.X : Polynomial ℝ) • A.map Polynomial.C).det
  have h := p.hasDerivAt 0
  rw [show p.derivative.eval 0 = A.trace from Matrix.derivative_det_one_add_X_smul A] at h
  have he : (fun t : ℝ => (1 + t • A).det) = (fun t => p.eval t) := by
    funext t
    change _ = (Polynomial.evalRingHom t) p
    rw [RingHom.map_det]
    congr 1
    ext i j
    change (if i = j then 1 else 0) + t * A i j =
      Polynomial.eval t ((if i = j then 1 else 0) +
        Polynomial.X * Polynomial.C (A i j))
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
    split_ifs <;> simp only [Polynomial.eval_one, Polynomial.eval_zero]
  rwa [he]

lemma hasDerivAt_det_add (D E : Matrix R R ℝ) (hD : IsUnit D) :
    HasDerivAt (fun t : ℝ => (D + t • E).det)
      (D.det * (D⁻¹ * E).trace) 0 := by
  have h := (hasDerivAt_det_one_add (D⁻¹ * E)).const_mul D.det
  have he : (fun t : ℝ => (D + t • E).det) =
      (fun t => D.det * (1 + t • (D⁻¹ * E)).det) := by
    funext t
    rw [← Matrix.det_mul]
    congr 1
    rw [mul_add, mul_one, mul_smul_comm, ← mul_assoc,
      Matrix.mul_nonsing_inv D ((Matrix.isUnit_iff_isUnit_det D).mp hD), one_mul]
  rwa [he]

lemma derivative_nonpos_at_right_max {f : ℝ → ℝ} {c : ℝ}
    (h : HasDerivAt f c 0) (hm : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t ≤ f 0) : c ≤ 0 := by
  have he : IsLocalMaxOn f (Set.Icc (0 : ℝ) 1) 0 :=
    (show IsMaxOn f (Set.Icc (0 : ℝ) 1) 0 from hm).localize
  have ht : (1 : ℝ) ∈ posTangentConeAt (Set.Icc (0 : ℝ) 1) 0 := by
    apply mem_posTangentConeAt_of_segment_subset
    simp [segment_eq_Icc]
  simpa using he.hasFDerivWithinAt_nonpos h.hasFDerivAt.hasFDerivWithinAt ht

lemma trace_inv_mul_le_of_det_max (D B : Matrix R R ℝ) (hD : D.PosDef)
    (hm : ∀ t ∈ Set.Icc (0 : ℝ) 1, (D + t • (B - D)).det ≤ D.det) :
    (D⁻¹ * B).trace ≤ (Fintype.card R : ℝ) := by
  have hd : 0 < D.det := hD.det_pos
  have he := derivative_nonpos_at_right_max (hasDerivAt_det_add D (B - D) hD.isUnit)
    (by simpa using hm)
  have ht : (D⁻¹ * (B - D)).trace ≤ 0 := by nlinarith
  rw [mul_sub, Matrix.trace_sub, Matrix.nonsing_inv_mul D ((Matrix.isUnit_iff_isUnit_det D).mp hD.isUnit), Matrix.trace_one] at ht
  linarith

lemma exists_regularized_det_max [Fintype I] [Nonempty I]
    (B : I → Matrix R R ℝ) (hB : ∀ i, (B i).PosSemidef)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ D : Matrix R R ℝ, D.PosDef ∧
      D ∈ (fun A => ε • (1 : Matrix R R ℝ) + A) '' convexHull ℝ (Set.range B) ∧
      ∀ i, (D⁻¹ * B i).trace ≤ (Fintype.card R : ℝ) := by
  let S := convexHull ℝ (Set.range B)
  let f : Matrix R R ℝ → Matrix R R ℝ := fun A => ε • (1 : Matrix R R ℝ) + A
  have hc : IsCompact S := (Set.finite_range B).isCompact_convexHull ℝ
  have hn : S.Nonempty := (Set.range_nonempty B).mono (subset_convexHull ℝ _)
  have hf : Continuous f := by fun_prop
  have hp : ∀ A ∈ S, A.PosSemidef :=
    convexHull_min (Set.range_subset_iff.mpr hB) convex_posSemidef
  have hpd : ∀ D ∈ f '' S, D.PosDef := by
    rintro _ ⟨A, hA, rfl⟩
    exact (Matrix.PosDef.one.smul hε).add_posSemidef (hp A hA)
  obtain ⟨D, hDs, hmax⟩ := (hc.image hf).exists_isMaxOn (hn.image f)
    (by fun_prop : ContinuousOn Matrix.det (f '' S))
  refine ⟨D, hpd D hDs, hDs, ?_⟩
  intro i
  have hi : f (B i) ∈ f '' S := ⟨B i, subset_convexHull ℝ _ (Set.mem_range_self i), rfl⟩
  have hs : Convex ℝ (f '' S) := by
    exact (convex_convexHull ℝ (Set.range B)).translate (ε • (1 : Matrix R R ℝ))
  have hm := trace_inv_mul_le_of_det_max D (f (B i)) (hpd D hDs) (by
    intro t ht
    apply hmax
    have he : D + t • (f (B i) - D) = (1 - t) • D + t • f (B i) := by module
    rw [he]
    exact hs hDs hi (sub_nonneg.mpr ht.2) ht.1 (by ring))
  have htr : 0 ≤ (D⁻¹).trace := (hpd D hDs).inv.posSemidef.trace_nonneg
  have he : (D⁻¹ * f (B i)).trace = ε * (D⁻¹).trace + (D⁻¹ * B i).trace := by
    simp [f, mul_add, Matrix.trace_add, Matrix.trace_smul]
  rw [he] at hm
  nlinarith

open scoped MatrixOrder

lemma trace_mul_nonneg {A B : Matrix R R ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  let G := CFC.sqrt B
  have hG : G.PosSemidef := (CFC.sqrt_nonneg B).posSemidef
  have hGG : G * G = B := CFC.sqrt_mul_sqrt_self B hB.nonneg
  have h := (hA.conjTranspose_mul_mul_same G).trace_nonneg
  rw [hG.isHermitian.eq, Matrix.trace_mul_cycle, hGG] at h
  simpa only [Matrix.trace_mul_comm B A] using h

lemma trace_mul_le_of_le {A B D : Matrix R R ℝ} (hA : A.PosSemidef) (hBD : B ≤ D) :
    (A * B).trace ≤ (A * D).trace := by
  have h := trace_mul_nonneg hA hBD
  rwa [mul_sub, Matrix.trace_sub, sub_nonneg] at h

lemma trace_mul_convexHull_le [Fintype I] (A : Matrix R R ℝ)
    (B : I → Matrix R R ℝ) (m : ℝ) (hB : ∀ i, (A * B i).trace ≤ m)
    {D : Matrix R R ℝ} (hD : D ∈ convexHull ℝ (Set.range B)) :
    (A * D).trace ≤ m := by
  have hc : Convex ℝ {D : Matrix R R ℝ | (A * D).trace ≤ m} := by
    intro X hX Y hY a b ha hb hab
    change (A * (a • X + b • Y)).trace ≤ m
    rw [mul_add, mul_smul_comm, mul_smul_comm, Matrix.trace_add,
      Matrix.trace_smul, Matrix.trace_smul]
    change a * (A * X).trace + b * (A * Y).trace ≤ m
    calc
      _ ≤ a * m + b * m := add_le_add
        (mul_le_mul_of_nonneg_left hX ha) (mul_le_mul_of_nonneg_left hY hb)
      _ = m := by rw [← add_mul, hab, one_mul]
  exact convexHull_min (Set.range_subset_iff.mpr hB) hc hD

lemma exists_normalized_factors [Fintype I] [Nonempty I] [Fintype J]
    (A : J → Matrix R R ℝ) (B : I → Matrix R R ℝ)
    (hA : ∀ j, (A j).PosSemidef) (hB : ∀ i, (B i).PosSemidef)
    (m : ℝ) (hpair : ∀ j i, (A j * B i).trace ≤ m) :
    ∃ (A' : J → Matrix R R ℝ) (B' : I → Matrix R R ℝ),
      (∀ j, (A' j).PosSemidef) ∧ (∀ i, (B' i).PosSemidef) ∧
      (∀ j i, (A' j * B' i).trace = (A j * B i).trace) ∧
      (∀ j, (A' j).trace ≤ m + 1) ∧
      (∀ i, (B' i).trace ≤ (Fintype.card R : ℝ)) := by
  classical
  let S : ℝ := ∑ j, (A j).trace
  have hS : 0 ≤ S := Finset.sum_nonneg (fun j _ => (hA j).trace_nonneg)
  let ε : ℝ := 1 / (1 + S)
  have hε : 0 < ε := one_div_pos.mpr (by linarith)
  have hεA (j : J) : ε * (A j).trace ≤ 1 := by
    have hj : (A j).trace ≤ S := Finset.single_le_sum
      (fun j _ => (hA j).trace_nonneg) (Finset.mem_univ j)
    change 1 / (1 + S) * (A j).trace ≤ 1
    rw [one_div_mul_eq_div]
    exact (div_le_one (by linarith : 0 < 1 + S)).mpr (by linarith)
  obtain ⟨D, hD, ⟨D₀, hD₀, hDeq⟩, htr⟩ := exists_regularized_det_max B hB ε hε
  let G := CFC.sqrt D
  have hG : G.PosSemidef := (CFC.sqrt_nonneg D).posSemidef
  have hGG : G * G = D := CFC.sqrt_mul_sqrt_self D hD.posSemidef.nonneg
  have huG : IsUnit G := (IsUnit.mul_iff.mp (hGG ▸ hD.isUnit)).1
  have hunit := (Matrix.isUnit_iff_isUnit_det G).mp huG
  have hGinv : G⁻¹.PosSemidef := hG.inv
  have hleft : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hunit
  have hright : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hunit
  have hinv : G⁻¹ * G⁻¹ = D⁻¹ := by
    rw [← hGG, Matrix.mul_inv_rev]
  refine ⟨fun j => G * A j * G, fun i => G⁻¹ * B i * G⁻¹,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    simpa only [hG.isHermitian.eq] using (hA j).conjTranspose_mul_mul_same G
  · intro i
    simpa only [hGinv.isHermitian.eq] using (hB i).conjTranspose_mul_mul_same G⁻¹
  · intro j i
    change (G * A j * G * (G⁻¹ * B i * G⁻¹)).trace = _
    have he : G * A j * G * (G⁻¹ * B i * G⁻¹) = G * (A j * B i) * G⁻¹ := by
      calc
        _ = G * A j * (G * G⁻¹) * B i * G⁻¹ := by simp only [mul_assoc]
        _ = _ := by rw [hright, mul_one]; simp only [mul_assoc]
    rw [he, Matrix.trace_mul_cycle, hleft, one_mul]
  · intro j
    rw [Matrix.trace_mul_cycle, hGG, Matrix.trace_mul_comm, ← hDeq, mul_add, Matrix.trace_add,
      mul_smul_comm, Matrix.trace_smul, mul_one]
    change ε * (A j).trace + (A j * D₀).trace ≤ m + 1
    have hl := trace_mul_convexHull_le (A j) B m (hpair j) hD₀
    linarith [hεA j]
  · intro i
    rw [Matrix.trace_mul_cycle, hinv]
    exact htr i

end PerfectMatchingPSD

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.SquareRootDisturbance ----
namespace OAI

universe u_1

namespace PerfectMatchingPSD
open Matrix
open scoped MatrixOrder Matrix.Norms.Frobenius
variable {R : Type u_1} [Fintype R] [DecidableEq R]

omit [DecidableEq R] in
lemma trace_mono_matrix {A B : Matrix R R ℝ} (h : A ≤ B) : A.trace ≤ B.trace :=
  (Matrix.tracePositiveLinearMap R ℝ ℝ).monotone h

lemma frobenius_sq (A : Matrix R R ℝ) :
    ‖A‖^2 = ∑ i, ∑ j, (A i j)^2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt]
  · simp
  · positivity

lemma frobenius_sq_trace (A : Matrix R R ℝ) : ‖A‖^2 = (Aᵀ * A).trace := by
  rw [frobenius_sq]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, ← pow_two]
  exact Finset.sum_comm

lemma square_le_self {A : Matrix R R ℝ} (hA : 0 ≤ A) (hA₁ : A ≤ 1) : A^2 ≤ A := by
  have hc : Commute A (1-A) := (Commute.one_right A).sub_right (Commute.refl A)
  have hh := Commute.mul_nonneg hA (sub_nonneg.mpr hA₁) hc
  simpa only [mul_sub, mul_one, ← pow_two, sub_nonneg] using hh

lemma transpose_mul_self_le_one {A : Matrix R R ℝ} (hA : 0 ≤ A) (hA₁ : A ≤ 1) :
    Aᵀ * A ≤ 1 := by
  have hh : Aᵀ = A := hA.posSemidef.isHermitian.eq
  rw [hh, ← pow_two]
  exact (square_le_self hA hA₁).trans hA₁

lemma frobenius_mul_contraction {A : Matrix R R ℝ} (hA : Aᵀ * A ≤ 1)
    (B : Matrix R R ℝ) : ‖A*B‖ ≤ ‖B‖ := by
  have h := hA.conjTranspose_mul_mul_same B
  have ht := h.trace_nonneg
  have hid : Bᴴ * (1 - Aᵀ * A) * B = Bᵀ * B - (A*B)ᵀ * (A*B) := by
    simp only [Matrix.conjTranspose_eq_transpose_of_trivial, mul_sub, sub_mul, mul_one,
      Matrix.transpose_mul, mul_assoc]
  rw [hid, Matrix.trace_sub, ← frobenius_sq_trace, ← frobenius_sq_trace] at ht
  nlinarith [norm_nonneg (A*B), norm_nonneg B]

lemma one_sub_square_le {A : Matrix R R ℝ} (hA : 0 ≤ A) (hA₁ : A ≤ 1) :
    (1-A)^2 ≤ 1-A := square_le_self (sub_nonneg.mpr hA₁) (by simpa using hA)

lemma test_error {ρ F : Matrix R R ℝ} (hρ : ρ.PosSemidef) (htρ : ρ.trace = 1)
    (hF : 0 ≤ F) (hF₁ : F ≤ 1) (ε : ℝ) (hε : 0 ≤ ε)
    (hs : 1-ε ≤ (ρ*F).trace) :
    ‖(F-1)*CFC.sqrt ρ‖ ≤ Real.sqrt ε := by
  let G := CFC.sqrt ρ
  have hG : G.PosSemidef := (CFC.sqrt_nonneg ρ).posSemidef
  have hGG : G*G = ρ := CFC.sqrt_mul_sqrt_self ρ hρ.nonneg
  have he : ((F-1)*G)ᵀ * ((F-1)*G) = G*(1-F)^2*G := by
    have hFt : Fᵀ = F := hF.posSemidef.isHermitian.eq
    have hGt : Gᵀ = G := hG.isHermitian.eq
    rw [Matrix.transpose_mul, Matrix.transpose_sub, hFt, Matrix.transpose_one, hGt]
    noncomm_ring
  have hb := trace_mul_le_of_le hρ (one_sub_square_le hF hF₁)
  have hnorm : ‖(F-1)*G‖^2 ≤ ε := by
    rw [frobenius_sq_trace, he, Matrix.trace_mul_cycle, hGG]
    have hc : (ρ*(1-F)).trace = 1-(ρ*F).trace := by
      rw [mul_sub, mul_one, Matrix.trace_sub, htρ]
    rw [hc] at hb
    linarith
  change ‖(F-1)*G‖ ≤ Real.sqrt ε
  nlinarith [Real.sq_sqrt hε, Real.sqrt_nonneg ε, norm_nonneg ((F-1)*G)]

lemma posSemidef_le_trace {A : Matrix R R ℝ} (hA : A.PosSemidef) :
    A ≤ A.trace • (1 : Matrix R R ℝ) := by
  classical
  have he (i : R) : hA.isHermitian.eigenvalues i ≤ A.trace := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues]
    exact Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
  have hd : (A.trace • (1 : Matrix R R ℝ) -
      Matrix.diagonal hA.isHermitian.eigenvalues).PosSemidef := by
    rw [Matrix.smul_one_eq_diagonal, Matrix.diagonal_sub]
    exact Matrix.PosSemidef.diagonal (fun i => sub_nonneg.mpr (he i))
  let U : Matrix R R ℝ := hA.isHermitian.eigenvectorUnitary
  have hu : U * Uᴴ = 1 := Unitary.coe_mul_star_self _
  have hs : A = U * Matrix.diagonal hA.isHermitian.eigenvalues * Uᴴ := by
    simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, U] using hA.isHermitian.spectral_theorem
  have hc := hd.conjTranspose_mul_mul_same Uᴴ
  have hc' : (A.trace • (1 : Matrix R R ℝ) -
      U * Matrix.diagonal hA.isHermitian.eigenvalues * Uᴴ).PosSemidef := by
    simpa only [Matrix.conjTranspose_conjTranspose, mul_sub, sub_mul,
      mul_smul_comm, smul_mul_assoc, mul_one, hu] using hc
  rwa [← hs] at hc'

end PerfectMatchingPSD

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.SequentialTests ----
namespace OAI

universe u_1 u_2

namespace PerfectMatchingPSD
open Matrix
open scoped MatrixOrder Matrix.Norms.Frobenius
variable {R : Type u_1} [Fintype R] [DecidableEq R]

omit [DecidableEq R] in
lemma congruence_mono {A B : Matrix R R ℝ} (h : A ≤ B) (X : Matrix R R ℝ) :
    Xᵀ * A * X ≤ Xᵀ * B * X := by
  change (Xᵀ * B * X - Xᵀ * A * X).PosSemidef
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, mul_sub, sub_mul]
    using h.conjTranspose_mul_mul_same X

omit [Fintype R] in
lemma effect_le_one (F : Bool → Matrix R R ℝ) (hF : ∀ b, 0 ≤ F b)
    (hs : F false + F true ≤ 1) (b : Bool) : F b ≤ 1 := by
  cases b
  · exact (le_add_of_nonneg_right (hF true)).trans hs
  · exact (le_add_of_nonneg_left (hF false)).trans hs

lemma effects_square_sum_le (F : Bool → Matrix R R ℝ) (hF : ∀ b, 0 ≤ F b)
    (hs : F false + F true ≤ 1) :
    (F false)ᵀ * F false + (F true)ᵀ * F true ≤ 1 := by
  have h0 : (F false)ᵀ = F false := (hF false).posSemidef.isHermitian.eq
  have h1 : (F true)ᵀ = F true := (hF true).posSemidef.isHermitian.eq
  rw [h0, h1, ← pow_two, ← pow_two]
  exact (add_le_add (square_le_self (hF false) (effect_le_one F hF hs false))
    (square_le_self (hF true) (effect_le_one F hF hs true))).trans hs

lemma sum_function_succ {q : ℕ} {A : Type u_2} [AddCommMonoid A]
    (f : (Fin (q+1) → Bool) → A) :
    ∑ y, f y = ∑ z : Fin q → Bool, (f (Fin.cons false z) + f (Fin.cons true z)) := by
  rw [← (Fin.consEquiv (fun _ : Fin (q+1) => Bool)).sum_comp f,
    Fintype.sum_prod_type, Finset.sum_comm]
  simp [Fin.consEquiv, add_comm]

lemma sequentialProduct_sum_le {q : ℕ} (F : Fin q → Bool → Matrix R R ℝ)
    (hF : ∀ i b, 0 ≤ F i b) (hs : ∀ i, F i false + F i true ≤ 1) :
    ∑ y, (sequentialProduct F y)ᵀ * sequentialProduct F y ≤ 1 := by
  induction q with
  | zero => simp [sequentialProduct]
  | succ q ih =>
    rw [sum_function_succ]
    apply le_trans _ (ih (Fin.tail F) (fun i => hF i.succ) (fun i => hs i.succ))
    apply Finset.sum_le_sum
    intro z _
    simp only [sequentialProduct, Fin.cons_zero, Fin.tail_cons, Matrix.transpose_mul]
    have h := congruence_mono (effects_square_sum_le (F 0) (hF 0) (hs 0))
      (sequentialProduct (Fin.tail F) z)
    simpa only [mul_add, add_mul, mul_one, mul_assoc] using h

lemma sequentialProduct_error {q : ℕ} (F : Fin q → Bool → Matrix R R ℝ)
    (y : Fin q → Bool) (G : Matrix R R ℝ) (δ : ℝ)
    (hF : ∀ i b, (F i b)ᵀ * F i b ≤ 1)
    (herr : ∀ i, ‖(F i (y i)-1)*G‖ ≤ δ) :
    ‖(sequentialProduct F y-1)*G‖ ≤ (q:ℝ)*δ := by
  induction q with
  | zero => simp [sequentialProduct]
  | succ q ih =>
    have ht := ih (Fin.tail F) (Fin.tail y)
      (fun i b => hF i.succ b) (fun i => herr i.succ)
    have hid : (sequentialProduct F y-1)*G =
        F 0 (y 0) * ((sequentialProduct (Fin.tail F) (Fin.tail y)-1)*G) +
          (F 0 (y 0)-1)*G := by
      simp only [sequentialProduct]
      noncomm_ring
    rw [hid]
    calc
      _ ≤ ‖F 0 (y 0) * ((sequentialProduct (Fin.tail F) (Fin.tail y)-1)*G)‖ +
          ‖(F 0 (y 0)-1)*G‖ := norm_add_le _ _
      _ ≤ (q:ℝ)*δ + δ := add_le_add
        ((frobenius_mul_contraction (hF 0 (y 0)) _).trans ht) (herr 0)
      _ = _ := by push_cast; ring

lemma norm_sqrt_trace_one {ρ : Matrix R R ℝ} (hρ : ρ.PosSemidef) (htρ : ρ.trace = 1) :
    ‖CFC.sqrt ρ‖ = 1 := by
  have hG : (CFC.sqrt ρ).PosSemidef := (CFC.sqrt_nonneg ρ).posSemidef
  have hGt : (CFC.sqrt ρ)ᵀ = CFC.sqrt ρ := hG.isHermitian.eq
  have hsq : ‖CFC.sqrt ρ‖^2 = 1 := by
    rw [frobenius_sq_trace, hGt, CFC.sqrt_mul_sqrt_self ρ hρ.nonneg, htρ]
  nlinarith [norm_nonneg (CFC.sqrt ρ)]

lemma norm_mul_sqrt_sq {ρ : Matrix R R ℝ} (hρ : ρ.PosSemidef)
    (V : Matrix R R ℝ) : ‖V*CFC.sqrt ρ‖^2 = (ρ*(Vᵀ*V)).trace := by
  let G := CFC.sqrt ρ
  have hGt : Gᵀ = G := (CFC.sqrt_nonneg ρ).posSemidef.isHermitian.eq
  have hGG : G*G = ρ := CFC.sqrt_mul_sqrt_self ρ hρ.nonneg
  change ‖V*G‖^2 = _
  rw [frobenius_sq_trace, Matrix.transpose_mul, hGt]
  have hid : G*Vᵀ*(V*G) = G*(Vᵀ*V)*G := by simp only [mul_assoc]
  rw [hid, Matrix.trace_mul_cycle, hGG]

lemma norm_mul_sq_lower (G V : Matrix R R ℝ) (hG : ‖G‖ = 1)
    (δ : ℝ) (hδ : δ ≤ 1/4) (he : ‖(V-1)*G‖ ≤ δ) :
    1/2 ≤ ‖V*G‖^2 := by
  have hh := norm_sub_le (V*G) ((V-1)*G)
  have hid : V*G - (V-1)*G = G := by rw [sub_mul, one_mul, sub_sub_cancel]
  rw [hid, hG] at hh
  nlinarith [sq_nonneg (‖V*G‖-3/4)]

lemma trace_product_upper {ρ : Matrix R R ℝ} (hρ : ρ.PosSemidef)
    (htρ : ρ.trace = 1) (V : Matrix R R ℝ) :
    (ρ*(Vᵀ*V)).trace ≤ (Vᵀ*V).trace := by
  have hρle : ρ ≤ 1 := by simpa only [htρ, one_smul] using posSemidef_le_trace hρ
  have hp : (Vᵀ*V).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial]
      using Matrix.posSemidef_conjTranspose_mul_self V
  have hub := trace_mul_le_of_le hp hρle
  rwa [Matrix.trace_mul_comm (Vᵀ*V) ρ, mul_one] at hub

lemma sequentialProduct_trace_lower {q : ℕ}
    (ρ : Matrix R R ℝ) (F : Fin q → Bool → Matrix R R ℝ) (y : Fin q → Bool)
    (hρ : ρ.PosSemidef) (htρ : ρ.trace = 1)
    (hF : ∀ i b, 0 ≤ F i b) (hpair : ∀ i, F i false + F i true ≤ 1)
    (ε : ℝ) (hε : 0 ≤ ε) (hsmall : (q:ℝ)*Real.sqrt ε ≤ 1/4)
    (hsuccess : ∀ i, 1-ε ≤ (ρ * F i (y i)).trace) :
    1/2 ≤ ((sequentialProduct F y)ᵀ * sequentialProduct F y).trace := by
  have heffect (i : Fin q) (b : Bool) : F i b ≤ 1 :=
    effect_le_one (F i) (hF i) (hpair i) b
  have hlocal (i : Fin q) : ‖(F i (y i)-1)*CFC.sqrt ρ‖ ≤ Real.sqrt ε :=
    test_error hρ htρ (hF i (y i)) (heffect i (y i)) ε hε (hsuccess i)
  have he := sequentialProduct_error F y (CFC.sqrt ρ) (Real.sqrt ε)
    (fun i b => transpose_mul_self_le_one (hF i b) (heffect i b)) hlocal
  have hsq := norm_mul_sq_lower (CFC.sqrt ρ) (sequentialProduct F y)
    (norm_sqrt_trace_one hρ htρ) _ hsmall he
  rw [norm_mul_sqrt_sq hρ] at hsq
  exact hsq.trans (trace_product_upper hρ htρ _)

lemma nearly_perfect_bit_tests {q : ℕ}
    (ρ : (Fin q → Bool) → Matrix R R ℝ) (F : Fin q → Bool → Matrix R R ℝ)
    (hρ : ∀ y, (ρ y).PosSemidef) (htρ : ∀ y, (ρ y).trace = 1)
    (hF : ∀ i b, 0 ≤ F i b) (hpair : ∀ i, F i false + F i true ≤ 1)
    (ε : ℝ) (hε : 0 ≤ ε) (hsmall : (q:ℝ)*Real.sqrt ε ≤ 1/4)
    (hsuccess : ∀ y i, 1-ε ≤ (ρ y * F i (y i)).trace) :
    (2:ℝ)^q / 2 ≤ Fintype.card R := by
  classical
  have hper (y : Fin q → Bool) :
      1/2 ≤ ((sequentialProduct F y)ᵀ * sequentialProduct F y).trace :=
    sequentialProduct_trace_lower (ρ y) F y (hρ y) (htρ y) hF hpair ε hε hsmall
      (hsuccess y)
  have hsum := Finset.sum_le_sum (fun y (_ : y ∈ Finset.univ) => hper y)
  have hupper := trace_mono_matrix (sequentialProduct_sum_le F hF hpair)
  rw [Matrix.trace_sum, Matrix.trace_one] at hupper
  have hcard : (∑ _y : Fin q → Bool, (1/2:ℝ)) = (2:ℝ)^q/2 := by
    simp [Fintype.card_bool, Fintype.card_fin, div_eq_mul_inv]
  rw [hcard] at hsum
  exact hsum.trans hupper

end PerfectMatchingPSD

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.BitTests ----
namespace OAI

universe u_1

namespace PerfectMatchingPSD
open Matrix
open scoped MatrixOrder
variable {R : Type u_1} [Fintype R] [DecidableEq R]

lemma two_div_success {μ ε : ℝ} (hμ : 2 ≤ μ) (hε : 0 ≤ ε) (hub : μ ≤ 2+ε) :
    1-ε ≤ 2/μ := by
  rw [le_div_iff₀ (by linarith : 0 < μ)]
  have hh : ε ≤ ε*μ := by nlinarith
  nlinarith

lemma normalized_gauge_pair (G Q T : Matrix R R ℝ) (hu : IsUnit G) :
    (G*Q*G*(G⁻¹*T*G⁻¹)).trace = (Q*T).trace := by
  have hunit := (Matrix.isUnit_iff_isUnit_det G).mp hu
  have hl : G⁻¹*G=1 := Matrix.nonsing_inv_mul G hunit
  have hr : G*G⁻¹=1 := Matrix.mul_nonsing_inv G hunit
  have he : G*Q*G*(G⁻¹*T*G⁻¹) = G*(Q*T)*G⁻¹ := by
    calc
      _ = G*Q*(G*G⁻¹)*T*G⁻¹ := by simp only [mul_assoc]
      _ = _ := by rw [hr, mul_one]; simp only [mul_assoc]
  rw [he, Matrix.trace_mul_cycle, hl, one_mul]

lemma inverse_sqrt_congruence (D : Matrix R R ℝ) (hD : D.PosDef) :
    (CFC.sqrt D)⁻¹ * D * (CFC.sqrt D)⁻¹ = 1 := by
  let G := CFC.sqrt D
  have hGG : G*G=D := CFC.sqrt_mul_sqrt_self D hD.posSemidef.nonneg
  have hu : IsUnit G := (IsUnit.mul_iff.mp (hGG ▸ hD.isUnit)).1
  have hl : G⁻¹*G=1 := Matrix.nonsing_inv_mul G ((Matrix.isUnit_iff_isUnit_det G).mp hu)
  have hr : G*G⁻¹=1 := Matrix.mul_nonsing_inv G ((Matrix.isUnit_iff_isUnit_det G).mp hu)
  change G⁻¹*D*G⁻¹=1
  rw [← hGG, ← mul_assoc, hl, one_mul, hr]

lemma states_of_domination {q : ℕ}
    (Q : (Fin q → Bool) → Matrix R R ℝ) (T : Fin q → Bool → Matrix R R ℝ)
    (D : Matrix R R ℝ) (hD : D.PosDef)
    (hQ : ∀ y, (Q y).PosSemidef) (hT : ∀ i b, (T i b).PosSemidef)
    (hdom : ∀ i, T i false + T i true ≤ D)
    (ε : ℝ) (hε : 0 ≤ ε)
    (htr : ∀ y, 2 ≤ (Q y*D).trace ∧ (Q y*D).trace ≤ 2+ε)
    (hbit : ∀ y i, (Q y * T i (y i)).trace = 2) :
    ∃ (ρ : (Fin q → Bool) → Matrix R R ℝ) (F : Fin q → Bool → Matrix R R ℝ),
      (∀ y, (ρ y).PosSemidef) ∧ (∀ y, (ρ y).trace = 1) ∧
      (∀ i b, 0 ≤ F i b) ∧ (∀ i, F i false + F i true ≤ 1) ∧
      ∀ y i, 1-ε ≤ (ρ y*F i (y i)).trace := by
  let G := CFC.sqrt D
  have hG : G.PosSemidef := (CFC.sqrt_nonneg D).posSemidef
  have hGG : G*G=D := CFC.sqrt_mul_sqrt_self D hD.posSemidef.nonneg
  have hu : IsUnit G := (IsUnit.mul_iff.mp (hGG ▸ hD.isUnit)).1
  have hGi : G⁻¹.PosSemidef := hG.inv
  let μ := fun y => (Q y*D).trace
  have hμ (y : Fin q → Bool) : 0 < μ y := lt_of_lt_of_le (by norm_num) (htr y).1
  refine ⟨fun y => (μ y)⁻¹ • (G*Q y*G), fun i b => G⁻¹*T i b*G⁻¹,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    apply Matrix.PosSemidef.smul _ (le_of_lt (inv_pos.mpr (hμ y)))
    simpa only [hG.isHermitian.eq] using (hQ y).conjTranspose_mul_mul_same G
  · intro y
    rw [Matrix.trace_smul, Matrix.trace_mul_cycle, hGG, Matrix.trace_mul_comm]
    change (μ y)⁻¹ * μ y = 1
    exact inv_mul_cancel₀ (ne_of_gt (hμ y))
  · intro i b
    apply Matrix.PosSemidef.nonneg
    simpa only [hGi.isHermitian.eq] using (hT i b).conjTranspose_mul_mul_same G⁻¹
  · intro i
    have hg := congruence_mono (hdom i) G⁻¹
    have hGit : (G⁻¹)ᵀ=G⁻¹ := hGi.isHermitian.eq
    rw [hGit, inverse_sqrt_congruence D hD, mul_add, add_mul] at hg
    exact hg
  · intro y i
    rw [smul_mul_assoc, Matrix.trace_smul, normalized_gauge_pair G (Q y) (T i (y i)) hu,
      hbit y i]
    change 1-ε ≤ (μ y)⁻¹*2
    rw [mul_comm, ← div_eq_mul_inv]
    exact two_div_success (htr y).1 hε (htr y).2

end PerfectMatchingPSD

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.MatrixBounds ----
namespace OAI

universe u_1 u_2

namespace PerfectMatchingPSD
open Matrix
open scoped MatrixOrder
variable {R : Type u_1} [Fintype R] [DecidableEq R]

lemma entry_product_bound {a x y b : ℝ} (hb : 0 ≤ b) (ha : |a| ≤ b) :
    x*a*y ≤ b*(x^2+y^2)/2 := by
  have hxy : 2 * |x| * |y| ≤ x^2+y^2 := by
    nlinarith [sq_nonneg (|x|-|y|), sq_abs x, sq_abs y]
  have he : x*a*y ≤ b*(|x| * |y|) := by
    calc
      _ ≤ |x*a*y| := le_abs_self _
      _ = |a| *(|x| * |y|) := by rw [abs_mul, abs_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ha (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  nlinarith [mul_le_mul_of_nonneg_left hxy hb]

lemma le_card_entry_bound {E : Matrix R R ℝ} (hE : E.IsHermitian)
    {b : ℝ} (hb : 0 ≤ b) (hbound : ∀ i j, |E i j| ≤ b) :
    E ≤ ((Fintype.card R : ℝ)*b) • (1 : Matrix R R ℝ) := by
  apply sub_nonneg.mp
  apply Matrix.PosSemidef.nonneg
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (isHermitian_one.smul (.of_nonneg (mul_nonneg (Nat.cast_nonneg _) hb))).sub hE
  · intro x
    have hsum : (∑ i, ∑ j, x i*E i j*x j) ≤
        (Fintype.card R : ℝ)*b*(∑ i, (x i)^2) := by
      calc
        _ ≤ ∑ i, ∑ j, (b/2*(x i)^2 + b/2*(x j)^2) := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          have he := entry_product_bound (x := x i) (y := x j) hb (hbound i j)
          linarith
        _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul, ← Finset.mul_sum]
          ring
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, star_trivial]
    rw [sub_nonneg]
    simpa only [dotProduct, Matrix.mulVec, Finset.mul_sum, pow_two, smul_eq_mul, mul_assoc] using hsum

lemma posSemidef_entry_abs_le_trace {A : Matrix R R ℝ} (hA : A.PosSemidef) (i j : R) :
    |A i j| ≤ A.trace := by
  have hi : 0 ≤ A i i := by
    have he := hA.dotProduct_mulVec_nonneg (Pi.single i 1)
    simpa using he
  have hj : 0 ≤ A j j := by
    have he := hA.dotProduct_mulVec_nonneg (Pi.single j 1)
    simpa using he
  have hsym : A j i = A i j := by
    simpa using congrArg (fun M : Matrix R R ℝ => M i j) hA.isHermitian.eq
  have hplus : -(A i i + A j j)/2 ≤ A i j := by
    have he := hA.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j 1)
    simp only [star_trivial, Matrix.mulVec_add, dotProduct_add,
      add_dotProduct, Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply] at he
    rw [hsym] at he
    linarith
  have hminus : A i j ≤ (A i i + A j j)/2 := by
    have he := hA.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
    simp only [star_trivial, Matrix.mulVec_sub, dotProduct_sub,
      sub_dotProduct, Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply] at he
    rw [hsym] at he
    linarith
  have hdiag (k : R) : A k k ≤ A.trace := by
    change A k k ≤ ∑ l, A l l
    apply Finset.single_le_sum (f := fun l => A l l)
    · intro l _
      have he := hA.dotProduct_mulVec_nonneg (Pi.single l 1)
      simpa using he
    · exact Finset.mem_univ k
  exact (abs_le.mpr ⟨by linarith, hminus⟩).trans (by linarith [hdiag i, hdiag j])

omit [Fintype R] [DecidableEq R] in
lemma matrix_sum_psd {X : Type u_2} (s : Finset X) (f : X → Matrix R R ℝ)
    (hf : ∀ x ∈ s, (f x).PosSemidef) : (∑ x ∈ s, f x).PosSemidef :=
  (Finset.sum_nonneg (fun x hx => (hf x hx).nonneg)).posSemidef

end PerfectMatchingPSD

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.MatrixAverages ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace PerfectMatchingPSD
open Matrix MatchingSmoothing
open scoped BigOperators MatrixOrder
attribute [local instance] Classical.propDecidable
variable {R : Type u_1} {X : Type u_2} [Fintype R] [DecidableEq R] [Fintype X]

omit [Fintype R] [DecidableEq R] in
lemma matrix_expect_eq (f : X → Matrix R R ℝ) :
    (𝔼 x, f x) = ((Fintype.card X : ℝ)⁻¹) • (∑ x, f x) := by
  ext i j
  simp [Finset.expect, NNRat.smul_def]

omit [Fintype R] [DecidableEq R] in
lemma matrix_expect_apply (f : X → Matrix R R ℝ) (u v : R) :
    (𝔼 x, f x) u v = 𝔼 x, f x u v := by
  rw [matrix_expect_eq, Fintype.expect_eq_sum_div_card]
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, div_eq_inv_mul]

omit [Fintype R] [DecidableEq R] in
lemma matrix_expect_psd (f : X → Matrix R R ℝ) (hf : ∀ x, (f x).PosSemidef) :
    (𝔼 x, f x).PosSemidef := by
  rw [matrix_expect_eq]
  exact (matrix_sum_psd Finset.univ f (fun x _ => hf x)).smul
    (inv_nonneg.mpr (Nat.cast_nonneg _))

lemma trace_mul_expect (Q : Matrix R R ℝ) (f : X → Matrix R R ℝ) :
    (Q * (𝔼 x, f x)).trace = 𝔼 x, (Q*f x).trace := by
  rw [matrix_expect_eq, mul_smul_comm, Matrix.trace_smul,
    Finset.mul_sum, Matrix.trace_sum, Fintype.expect_eq_sum_div_card]
  change (Fintype.card X : ℝ)⁻¹ * _ = _ / Fintype.card X
  rw [div_eq_inv_mul]

lemma expect_abs_bound (f : X → ℝ) {b : ℝ} (hb : 0 ≤ b) (hf : ∀ x, |f x| ≤ b) :
    |𝔼 x, f x| ≤ b := by
  by_cases hX : Nonempty X
  · let := hX
    have h0 (x : X) : -b ≤ f x := (abs_le.mp (hf x)).1
    have h1 (x : X) : f x ≤ b := (abs_le.mp (hf x)).2
    apply abs_le.mpr
    constructor
    · simpa using Finset.expect_le_expect (s := Finset.univ) (fun x _ => h0 x)
    · simpa using Finset.expect_le_expect (s := Finset.univ) (fun x _ => h1 x)
  · have : IsEmpty X := not_nonempty_iff.mp hX
    simpa using hb

section CellMatrices
variable {A : Type u_3} {B : Type u_4} {C : Type u_5} {I : Type u_6} [Fintype A] [Fintype B] [Fintype C] [Fintype I] [DecidableEq I]

omit [Fintype R] [DecidableEq R] in
lemma cellMatrix_apply (i : I) (Bf : Pairing ((A ⊕ B) ⊕ (I × C)) → Matrix R R ℝ)
    (x : Fin 3 → ℝ) (u v : R) :
    cellMatrix i Bf x u v = cellAverage i (fun M => Bf M u v) x := by
  rw [cellAverage, predicateAverage_eq_expect]
  simp only [cellMatrix, extensionMatrix, extensionAverage, matrix_expect_apply]
  apply Finset.expect_congr (by ext; simp)
  intro M _
  rfl

omit [Fintype R] [DecidableEq R] in
lemma cellMatrix_psd (i : I) (Bf : Pairing ((A ⊕ B) ⊕ (I × C)) → Matrix R R ℝ)
    (hB : ∀ M, (Bf M).PosSemidef) (x : Fin 3 → ℝ) :
    (cellMatrix i Bf x).PosSemidef := by
  apply matrix_expect_psd
  intro M
  apply matrix_expect_psd
  intro N
  exact hB _

omit [Fintype R] [DecidableEq R] in
lemma cellMatrix_star (i j : I) (Bf : Pairing ((A ⊕ B) ⊕ (I × C)) → Matrix R R ℝ)
    (x : ℝ) : cellMatrix i Bf ![x,0,0] = cellMatrix j Bf ![x,0,0] := by
  ext u v
  simp only [cellMatrix_apply, cellAverage_star]

lemma trace_cellMatrix (i : I) (Bf : Pairing ((A ⊕ B) ⊕ (I × C)) → Matrix R R ℝ)
    (Q : Matrix R R ℝ) (x : Fin 3 → ℝ) :
    (Q*cellMatrix i Bf x).trace = cellAverage i (fun M => (Q*Bf M).trace) x := by
  rw [cellAverage, predicateAverage_eq_expect, cellMatrix, trace_mul_expect]
  apply Finset.expect_congr (by ext; simp)
  intro M _
  exact trace_mul_expect Q _

omit [Fintype A] [Fintype B] in
lemma extensionAverage_sq_bound (i : I)
    (Bf : Pairing ((A ⊕ B) ⊕ (I × C)) → Matrix R R ℝ)
    (hB : ∀ M, (Bf M).PosSemidef) {b : ℝ} (hb : 0 ≤ b)
    (htr : ∀ M, (Bf M).trace ≤ b) (u v : R) (M : Pairing ((A ⊕ B) ⊕ C)) :
    (extensionAverage i (fun N => Bf N u v) M)^2 ≤ b^2 := by
  have he := expect_abs_bound (fun N => Bf (extendLocal i M N) u v) hb
    (fun N => (posSemidef_entry_abs_le_trace (hB _) u v).trans (htr _))
  have hex : extensionAverage i (fun N => Bf N u v) M =
      𝔼 N : {j : I // j ≠ i} → Pairing C, Bf (extendLocal i M N) u v := by
    apply Finset.expect_congr (by ext; simp)
    intro N _
    rfl
  rw [hex]
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hb).mpr he

end CellMatrices
end PerfectMatchingPSD

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.PolynomialInterpolation ----
namespace OAI

namespace MatchingInterpolation
open Polynomial
open MatchingSmoothing

lemma power_interpolation (d k : ℕ) (hk : k ≤ d) (x : ℝ) :
    x^k = ∑ j : Fin (d+1), (j:ℝ)^k * (lagrange d j).eval x := by
  have hinj : Set.InjOn (fun j : Fin (d+1) => (j:ℝ)) (Finset.univ : Finset (Fin (d+1))) := by
    intro i _ j _ h
    apply Fin.ext
    change (i.val:ℝ) = (j.val:ℝ) at h
    exact Nat.cast_inj.mp h
  have hdeg : (Polynomial.X^k : ℝ[X]).degree < (Finset.univ : Finset (Fin (d+1))).card := by
    simp only [Polynomial.degree_X_pow, Finset.card_univ, Fintype.card_fin]
    exact_mod_cast Nat.lt_succ_of_le hk
  have he := congrArg (Polynomial.eval x) (Lagrange.eq_interpolate hinj hdeg)
  simpa [Lagrange.interpolate_apply, lagrange, Polynomial.eval_finsetSum] using he

lemma list_product_counts (l : List (Fin 3)) (x : Point) :
    (l.map x).prod = ∏ a, x a ^ l.count a := by
  rw [Finset.prod_list_map_count]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro a _ ha
  have hn : a ∉ l := fun hx => ha (List.mem_toFinset.mpr hx)
  simp [List.count_eq_zero_of_not_mem hn]

lemma monomial_interpolation (d : ℕ) (l : List (Fin 3)) (hl : l.length ≤ d) (x : Point) :
    (l.map x).prod = ∑ g : GridIndex d, tensorBasis d g x * (l.map (gridNode g)).prod := by
  rw [list_product_counts]
  have hp (a : Fin 3) := power_interpolation d (l.count a)
    (List.count_le_length.trans hl) (x a)
  simp_rw [hp]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.prod_mul_distrib, list_product_counts, mul_comm]
  rfl

lemma lowDegree_interpolation (d : ℕ) (P : Point → ℝ) (hP : P ∈ lowDegree coord d)
    (x : Point) : P x = ∑ g : GridIndex d, tensorBasis d g x * P (gridNode g) := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨l, hl, rfl⟩ := hP
    have he (v : Point) : (l.map coord).prod v = (l.map v).prod := by
      induction l with
      | nil => rfl
      | cons a l ih => simpa [coord] using congrArg (fun t => v a*t) (ih (by simpa only [List.length_cons] using Nat.le_trans (Nat.le_succ l.length) hl))
    simp_rw [he]
    exact monomial_interpolation d l hl x
  | zero => simp
  | add f g _ _ hf hg => simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hf, hg]
  | smul c f _ hf =>
    simp only [Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_comm _ c, Finset.mul_sum, hf]

lemma linePolynomial_eval (d : ℕ) (g : GridIndex d) (v : Point) (t : ℝ) :
    (linePolynomial d g v).eval t = tensorBasis d g (fun a => t * v a) := by
  simp only [linePolynomial, tensorBasis, Polynomial.eval_prod, Polynomial.eval_comp,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  apply Finset.prod_congr rfl
  intro a _
  rw [mul_comm]

lemma linePolynomial_zero (d : ℕ) (g : GridIndex d) (v : Point) :
    (linePolynomial d g v).coeff 0 = ∏ a, (lagrange d (g a)).eval 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, linePolynomial_eval]
  simp [tensorBasis]

lemma linePolynomial_one (d : ℕ) (g : GridIndex d) (v : Point) :
    (linePolynomial d g v).coeff 1 =
      ∑ a, v a * ((∏ b ∈ Finset.univ.erase a, (lagrange d (g b)).eval 0) *
        (lagrange d (g a)).derivative.eval 0) := by
  have he (P : ℝ[X]) : P.coeff 1 = P.derivative.eval 0 := by
    simp [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
  rw [he, linePolynomial, Polynomial.derivative_prod_finset, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Polynomial.derivative_comp, Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_X, zero_mul, mul_one, zero_add, Polynomial.eval_mul,
    Polynomial.eval_comp, Polynomial.eval_prod, Polynomial.eval_C, Polynomial.eval_X,
    mul_zero]
  ring

lemma weightPolynomial_zero (d : ℕ) (g : GridIndex d) :
    (weightPolynomial d g).coeff 0 = 0 := by
  simp only [weightPolynomial, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_smul, smul_eq_mul, linePolynomial_zero]
  ring

lemma weightPolynomial_one (d : ℕ) (g : GridIndex d) :
    (weightPolynomial d g).coeff 1 = 0 := by
  simp only [weightPolynomial, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_smul, smul_eq_mul, linePolynomial_one, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero, add_zero]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro a _
  fin_cases a <;> simp [dirA, dirB, dirStar, dirP]

lemma weightPolynomial_bound (d : ℕ) (g : GridIndex d) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ t ∈ Set.Icc (0:ℝ) 1,
      |(weightPolynomial d g).eval t| ≤ c * t^2 := by
  have hd : (Polynomial.X^2 : ℝ[X]) ∣ weightPolynomial d g := by
    apply Polynomial.X_pow_dvd_iff.mpr
    intro k hk
    interval_cases k
    · exact weightPolynomial_zero d g
    · exact weightPolynomial_one d g
  obtain ⟨P, hP⟩ := hd
  obtain ⟨b, hb⟩ := (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) 1)).exists_bound_of_continuousOn
    P.continuous.continuousOn
  refine ⟨max b 0, le_max_right _ _, ?_⟩
  intro t ht
  rw [hP, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, abs_mul,
    abs_of_nonneg (sq_nonneg t), mul_comm]
  have htbound : |P.eval t| ≤ b := by simpa only [Real.norm_eq_abs] using hb t ht
  exact mul_le_mul_of_nonneg_right (htbound.trans (le_max_left b 0)) (sq_nonneg t)

lemma weights_bound (d : ℕ) : ∃ c : ℝ, 0 < c ∧ ∀ L : ℝ, 1 ≤ L →
    ∀ g : GridIndex d, |weight d L g| ≤ c / L^2 := by
  classical
  choose c hc hb using weightPolynomial_bound d
  refine ⟨1 + ∑ g, c g, by have hsum := Finset.sum_nonneg (fun g (_ : g ∈ Finset.univ) => hc g); linarith, ?_⟩
  intro L hL g
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have ht : L⁻¹ ∈ Set.Icc (0:ℝ) 1 := ⟨inv_nonneg.mpr hLp.le,
    (inv_le_one₀ hLp).mpr hL⟩
  calc
    |weight d L g| ≤ c g * (L⁻¹)^2 := hb g L⁻¹ ht
    _ ≤ (1+∑ a, c a) * (L⁻¹)^2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have hh := Finset.single_le_sum (fun a (_ : a ∈ Finset.univ) => hc a)
        (Finset.mem_univ g)
      linarith
    _ = (1+∑ a, c a)/L^2 := by simp [div_eq_mul_inv]

lemma lowDegree_affine_pullback (d : ℕ) (P : Point → ℝ)
    (hP : P ∈ lowDegree coord d) (b : Point) (L : ℝ) :
    (fun x : Point => P (fun a => b a + L*x a)) ∈ lowDegree coord d := by
  have hcoord (a : Fin 3) : (fun x : Point => b a + L*x a) ∈ lowDegree coord 1 := by
    have hc := (lowDegree coord 1).smul_mem (b a) (one_mem_lowDegree coord 1)
    have hx := (lowDegree coord 1).smul_mem L (coord_mem_lowDegree coord a)
    convert (lowDegree coord 1).add_mem hc hx using 1
    ext x
    simp [coord]
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨l, hl, rfl⟩ := hP
    apply lowDegree_mono coord hl
    clear hl
    induction l with
    | nil => exact one_mem_lowDegree coord 0
    | cons a l ih =>
      convert mul_mem_lowDegree coord (hcoord a) ih using 1
      · simp only [List.length_cons, Nat.add_comm]
      · rfl
  | zero => exact (lowDegree coord d).zero_mem
  | add f g _ _ hf hg => exact (lowDegree coord d).add_mem hf hg
  | smul c f _ hf => exact (lowDegree coord d).smul_mem c hf

lemma weighted_interpolation (d : ℕ) (P : Point → ℝ) (hP : P ∈ lowDegree coord d)
    (L : ℝ) (hL : L ≠ 0) :
    P (origin + dirA) + P (origin + dirB) - P (origin + dirStar) -
      2 * P (origin + dirP) + P origin =
      ∑ g : GridIndex d, weight d L g * P (fun a => origin a + L*(g a:ℝ)) := by
  let Q : Point → ℝ := fun x => P (fun a => origin a + L*x a)
  have hQ : Q ∈ lowDegree coord d := lowDegree_affine_pullback d P hP origin L
  have he (v : Point) : P (origin + v) =
      ∑ g : GridIndex d, (linePolynomial d g v).eval L⁻¹ *
        P (fun a => origin a + L*(g a:ℝ)) := by
    have hi := lowDegree_interpolation d Q hQ (fun a => L⁻¹*v a)
    have hx : (fun a => origin a + L*(L⁻¹*v a)) = origin + v := by
      funext a
      simp [hL]
    simpa only [Q, hx, ← linePolynomial_eval, gridNode] using hi
  have he0 := he 0
  rw [add_zero] at he0
  rw [he dirA, he dirB, he dirStar, he dirP, he0]
  simp only [weight, weightPolynomial, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_smul, smul_eq_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    add_mul, sub_mul, mul_assoc, ← Finset.mul_sum]

end MatchingInterpolation

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.MatrixInterpolation ----
namespace OAI

universe u_1 u_2

namespace MatchingInterpolation
open MatchingSmoothing Matrix PerfectMatchingPSD
open scoped BigOperators MatrixOrder
attribute [local instance] Classical.propDecidable

lemma weightMass_nonneg (d : ℕ) (L : ℝ) : 0 ≤ weightMass d L :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma sum_abs_specialCoeff : (∑ j, |specialCoeff j|) = 6 := by
  norm_num [specialCoeff, Fin.sum_univ_succ]

lemma five_interpolation {d : ℕ} (P : Point → ℝ) (hP : P ∈ lowDegree coord d)
    {L : ℝ} (hL : L ≠ 0) :
    (∑ j, specialCoeff j * P (specialPoint j)) = ∑ g, weight d L g * P (scaledNode L g) := by
  have h := weighted_interpolation d P hP L hL
  simp only [specialCoeff, specialPoint, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, one_mul, neg_mul, Fin.sum_univ_zero, add_zero] at *
  change _ = ∑ g, weight d L g * P (fun a => origin a+L*(g a:ℝ))
  linarith

lemma finite_weighted_error {X : Type u_1} [Fintype X]
    (c e : X → ℝ) {η : ℝ} (he : ∀ x, |e x| ≤ η) :
    |∑ x, c x*e x| ≤ (∑ x, |c x|)*η := by
  calc
    _ ≤ ∑ x, |c x*e x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, |c x| *η := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (he x) (abs_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

lemma interpolation_error {d : ℕ} (F P : Point → ℝ)
    (hP : P ∈ lowDegree coord d) {L η : ℝ} (hL : L ≠ 0)
    (hs : ∀ j, |F (specialPoint j)-P (specialPoint j)| ≤ η)
    (hg : ∀ g : GridIndex d, |F (scaledNode L g)-P (scaledNode L g)| ≤ η) :
    |(∑ j, specialCoeff j*F (specialPoint j)) -
      ∑ g, weight d L g*F (scaledNode L g)| ≤ (6+weightMass d L)*η := by
  have hidentity : (∑ j, specialCoeff j*F (specialPoint j)) -
      ∑ g, weight d L g*F (scaledNode L g) =
    (∑ j, specialCoeff j*(F (specialPoint j)-P (specialPoint j))) -
      ∑ g, weight d L g*(F (scaledNode L g)-P (scaledNode L g)) := by
    simp only [mul_sub, Finset.sum_sub_distrib, five_interpolation P hP hL]
    ring
  rw [hidentity]
  have h1 := finite_weighted_error specialCoeff (fun j => F (specialPoint j)-P (specialPoint j)) hs
  have h2 := finite_weighted_error (weight d L) (fun g => F (scaledNode L g)-P (scaledNode L g)) hg
  rw [sum_abs_specialCoeff] at h1
  calc
    _ ≤ |∑ j, specialCoeff j*(F (specialPoint j)-P (specialPoint j))| +
        |∑ g, weight d L g*(F (scaledNode L g)-P (scaledNode L g))| := abs_sub _ _
    _ ≤ 6*η + weightMass d L*η := add_le_add h1 h2
    _ = _ := by ring

section Matrices
variable {R : Type u_2} [Fintype R] [DecidableEq R]

lemma interpolation_matrix_domination (d : ℕ)
    (B : Point → Matrix R R ℝ) (hB : ∀ x, (B x).PosSemidef)
    (P : R → R → Point → ℝ) (hP : ∀ u v, P u v ∈ lowDegree coord d)
    {L η : ℝ} (hL : L ≠ 0) (hη : 0 ≤ η)
    (hs : ∀ j u v, |B (specialPoint j) u v-P u v (specialPoint j)| ≤ η)
    (hg : ∀ g : GridIndex d, ∀ u v, |B (scaledNode L g) u v-P u v (scaledNode L g)| ≤ η) :
    ∃ E : Matrix R R ℝ, E.PosSemidef ∧
      B (origin+dirA)+B (origin+dirB) ≤ B (origin+dirStar)+(2:ℝ) • B (origin+dirP)+E ∧
      ∀ (Q : Matrix R R ℝ) (m k : ℝ), Q.trace ≤ m →
        (∀ g : GridIndex d, (Q*B (scaledNode L g)).trace ≤ k) →
        (Q*E).trace ≤ weightMass d L*k +
          (Fintype.card R : ℝ)*(6+weightMass d L)*η*m := by
  let H := (∑ j, specialCoeff j • B (specialPoint j)) -
    ∑ g, weight d L g • B (scaledNode L g)
  let b := (6+weightMass d L)*η
  let c := (Fintype.card R : ℝ)*b
  let W := ∑ g, |weight d L g| • B (scaledNode L g)
  have hb : 0 ≤ b := mul_nonneg (by linarith [weightMass_nonneg d L]) hη
  have hc : 0 ≤ c := mul_nonneg (Nat.cast_nonneg _) hb
  have hH : H.IsHermitian := by
    have hh (x : Point) := (hB x).isHermitian.eq
    simp only [H, Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_sum,
      Matrix.conjTranspose_smul, star_trivial, hh]
  have hentry (u v : R) : |H u v| ≤ b := by
    simpa only [H, Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using
      interpolation_error (fun x => B x u v) (P u v) (hP u v) hL (fun j => hs j u v) (fun g => hg g u v)
  have hbound : H ≤ c • (1 : Matrix R R ℝ) := le_card_entry_bound hH hb hentry
  have hW : W.PosSemidef := matrix_sum_psd _ _ (fun g _ => (hB _).smul (abs_nonneg _))
  let E := W+c • (1 : Matrix R R ℝ)
  have hE : E.PosSemidef := hW.add (Matrix.PosSemidef.one.smul hc)
  refine ⟨E,hE,?_,?_⟩
  · apply sub_nonneg.mp
    apply Matrix.PosSemidef.nonneg
    have hdiff : (∑ g : GridIndex d, (|weight d L g|-weight d L g) • B (scaledNode L g)).PosSemidef :=
      matrix_sum_psd _ _ (fun g _ => (hB _).smul (sub_nonneg.mpr (le_abs_self _)))
    convert ((sub_nonneg.mpr hbound).posSemidef.add (hB origin)).add hdiff using 1
    dsimp [E,W,H]
    simp only [sub_smul, Finset.sum_sub_distrib, specialPoint, specialCoeff, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, one_smul, neg_smul,
      Fin.sum_univ_zero, add_zero]
    module
  · intro Q m k hm hk
    change (Q*(W+c • (1 : Matrix R R ℝ))).trace ≤ _
    rw [mul_add, Matrix.trace_add, mul_smul_comm, Matrix.trace_smul, mul_one]
    have hWt : (Q*W).trace ≤ weightMass d L*k := by
      dsimp [W,weightMass]
      rw [Finset.mul_sum, Matrix.trace_sum, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro g _
      rw [mul_smul_comm, Matrix.trace_smul]
      exact mul_le_mul_of_nonneg_left (hk g) (abs_nonneg _)
    have he := add_le_add hWt (mul_le_mul_of_nonneg_left hm hc)
    calc
      _ ≤ weightMass d L*k + c*m := he
      _ = _ := by dsimp [c,b]; ring

end Matrices
end MatchingInterpolation

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.GoodCells ----
namespace OAI

namespace MatchingInterpolation
open MatchingSmoothing PerfectMatchingPSD Matrix
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma specialPoint_explicit (j : Fin 5) :
    specialPoint j = (![![1,0,0], ![0,1,1], ![3,0,0], ![1,2,0], ![1,0,2]] j : Point) := by
  fin_cases j <;> ext a <;> fin_cases a <;> norm_num [specialPoint, origin, dirP, dirStar, dirA, dirB]

lemma sample_witness {s l d : ℕ} (hs : 1 ≤ s) (hsl : 2*l*d ≤ s) (t : SampleIndex d) :
    ∃ M : Pairing (TripleVertices s), crossVector threeColor M = samplePoint d (2*l) t := by
  rcases t with j | g
  · rw [samplePoint, Sum.elim_inl, specialPoint_explicit]
    exact triple_pairing_five hs j
  · exact triple_pairing_grid hsl g

lemma good_cell_polynomials (K : ℕ) :
    ∃ d H : ℕ, 0 < d ∧ ∀ s q l r : ℕ, H ≤ 3*s+1 → 1 ≤ s → 2*l*d ≤ s →
      ∀ (B : Pairing (GlobalVertices s q) → Matrix (Fin r) (Fin r) ℝ),
      (∀ M, (B M).PosSemidef) → (∀ M, (B M).trace ≤ (r:ℝ)) →
      ∀ η : ℝ, 0 ≤ η →
      (q:ℝ)*r^4*(Fintype.card (SampleIndex d))*((2*(3*s+1):ℝ)^(2*K))⁻¹ ≤ η^2 →
      ∃ a : Equiv.Perm (GlobalVertices s q),
      ∃ P : Fin q → Fin r → Fin r → Point → ℝ,
        (∀ i u v, P i u v ∈ lowDegree coord d) ∧
        ∀ i u v t, |cellMatrix i (fun M => B (Pairing.relabel a M))
          (samplePoint d (2*l) t) u v-P i u v (samplePoint d (2*l) t)| ≤ η := by
  classical
  obtain ⟨d,H,hd,hmain⟩ := simultaneous_cross_approximation K
  refine ⟨d,H,hd,?_⟩
  intro s q l r hH hs hsl B hB htr η hη hnum
  let J := Fin q × (Fin r × Fin r)
  let T := SampleIndex d
  let M : T → Pairing (TripleVertices s) := fun t => (sample_witness hs hsl t).choose
  have hM (t : T) : crossVector threeColor (M t) = samplePoint d (2*l) t :=
    (sample_witness hs hsl t).choose_spec
  let g (j : J) (a : Equiv.Perm (GlobalVertices s q)) (N : Pairing (TripleVertices s)) : ℝ :=
    extensionAverage j.1 (fun Z => B (Pairing.relabel a Z) j.2.1 j.2.2) N
  have hg (j : J) (a : Equiv.Perm (GlobalVertices s q)) (p : Equiv.Perm (TripleVertices s)) :
      g j (a * liftLocal j.1 p) = fun N => g j a (Pairing.relabel p N) := by
    funext N
    dsimp only [g]
    rw [extensionAverage_relabel]
    simp only [Pairing.relabel_mul]
  have hgb (j : J) (a : Equiv.Perm (GlobalVertices s q)) (N : Pairing (TripleVertices s)) :
      (g j a N)^2 ≤ (r:ℝ)^2 :=
    extensionAverage_sq_bound j.1 _ (fun Z => hB _) (Nat.cast_nonneg r)
      (fun Z => htr _) j.2.1 j.2.2 N
  obtain ⟨a,P,hP,hbound⟩ := hmain (3*s+1) hH (TripleVertices s)
    (Equiv.Perm (GlobalVertices s q)) J T (tripleEquiv s) (fun _ => threeColor)
      (fun _ c => triple_histogram_pos (by omega) c) (fun _ => M)
      (fun j => liftLocal j.1) g hg (r:ℝ) hgb
  refine ⟨a,fun i u v => P (i,u,v),fun i u v => hP (i,u,v),?_⟩
  intro i u v t
  let E (j : J) (t : T) :=
    predicateAverage (fun N => crossVector threeColor N = crossVector threeColor (M t)) (g j a) -
      P j (crossVector threeColor (M t))
  have hjt : (E (i,u,v) t)^2 ≤ ∑ j, ∑ t, (E j t)^2 := by
    exact (Finset.single_le_sum (fun z _ => sq_nonneg (E (i,u,v) z)) (Finset.mem_univ t)).trans
      (Finset.single_le_sum (fun j _ => Finset.sum_nonneg (fun z _ => sq_nonneg (E j z)))
        (Finset.mem_univ (i,u,v)))
  have hb : (∑ j, ∑ t, (E j t)^2) ≤ η^2 := by
    apply hbound.trans
    have heq : (Fintype.card J : ℝ)*(Fintype.card T)*((2*(3*s+1:ℕ):ℝ)^(2*K))⁻¹*(r:ℝ)^2 =
        (q:ℝ)*r^4*(Fintype.card (SampleIndex d))*((2*(3*s+1):ℝ)^(2*K))⁻¹ := by
      simp only [J, T, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
      ring
    rw [heq]
    exact hnum
  have hab : |E (i,u,v) t| ≤ η := (sq_le_sq₀ (abs_nonneg _) hη).mp
    (by simpa only [sq_abs] using hjt.trans hb)
  have he : E (i,u,v) t = cellMatrix i (fun Z => B (Pairing.relabel a Z))
      (samplePoint d (2*l) t) u v-P (i,u,v) (samplePoint d (2*l) t) := by
    rw [cellMatrix_apply]
    dsimp only [E, cellAverage, g]
    rw [hM]
  rwa [he] at hab

end MatchingInterpolation

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.DominationDecoder ----
namespace OAI

universe u_1

namespace PerfectMatchingPSD
open Matrix
open scoped BigOperators MatrixOrder
attribute [local instance] Classical.propDecidable

lemma domination_decoder {R : Type u_1} [Fintype R] [DecidableEq R] {q : ℕ}
    (Q : (Fin q → Bool) → Matrix R R ℝ)
    (T : Fin q → Bool → Matrix R R ℝ) (P E : Fin q → Matrix R R ℝ)
    (S : Matrix R R ℝ)
    (hQ : ∀ y, (Q y).PosSemidef) (hT : ∀ i b, (T i b).PosSemidef)
    (hP : ∀ i, (P i).PosSemidef) (hE : ∀ i, (E i).PosSemidef) (hS : S.PosSemidef)
    (hdom : ∀ i, T i false + T i true ≤ S+(2:ℝ) • P i+E i)
    (hzero : ∀ y i, (Q y*P i).trace=0) (hstar : ∀ y, (Q y*S).trace=2)
    (hbit : ∀ y i, (Q y*T i (y i)).trace=2)
    {m e δ : ℝ} (hδ : 0 < δ) (hm : ∀ y, (Q y).trace ≤ m)
    (he : ∀ y i, (Q y*E i).trace ≤ e)
    (hε : 0 ≤ (q:ℝ)*e+δ*m)
    (hsmall : (q:ℝ)*Real.sqrt ((q:ℝ)*e+δ*m) ≤ 1/4) :
    (2:ℝ)^q/2 ≤ Fintype.card R := by
  let F := fun i => (2:ℝ) • P i+E i
  have hF (i : Fin q) : (F i).PosSemidef := (hP i).smul (by norm_num) |>.add (hE i)
  let D := S+(∑ i, F i)+δ • (1 : Matrix R R ℝ)
  have hsum : (∑ i, F i).PosSemidef := matrix_sum_psd _ _ (fun i _ => hF i)
  have hdelt : (δ • (1 : Matrix R R ℝ)).PosDef := Matrix.PosDef.one.smul hδ
  have hD : D.PosDef := by
    simpa only [D, add_comm] using hdelt.add_posSemidef (hS.add hsum)
  have hleS : S ≤ D := by
    have he := add_nonneg hsum.nonneg hdelt.posSemidef.nonneg
    dsimp [D]
    simpa only [add_assoc] using le_add_of_nonneg_right he
  have hdomD (i : Fin q) : T i false+T i true ≤ D := by
    apply (hdom i).trans
    have hi : F i ≤ ∑ j, F j := Finset.single_le_sum (fun j _ => (hF j).nonneg) (Finset.mem_univ i)
    calc
      S+(2:ℝ) • P i+E i = S+F i := by dsimp [F]; abel
      _ ≤ S+(∑ j, F j) := by simpa only [add_comm] using add_le_add_left hi S
      _ ≤ D := le_add_of_nonneg_right hdelt.posSemidef.nonneg
  have htr (y : Fin q → Bool) : 2 ≤ (Q y*D).trace ∧ (Q y*D).trace ≤ 2+((q:ℝ)*e+δ*m) := by
    constructor
    · rw [← hstar y]
      exact trace_mul_le_of_le (hQ y) hleS
    · dsimp [D]
      rw [mul_add, mul_add, Matrix.trace_add, Matrix.trace_add, hstar,
        Finset.mul_sum, Matrix.trace_sum, mul_smul_comm, Matrix.trace_smul, mul_one]
      have hsumtr : (∑ i, (Q y*F i).trace) ≤ (q:ℝ)*e := by
        have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => he y i)
        have hFi (i : Fin q) : (Q y*F i).trace = (Q y*E i).trace := by
          simp only [F, mul_add, Matrix.trace_add, mul_smul_comm, Matrix.trace_smul,
            hzero, smul_zero, zero_add]
        simpa only [hFi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hh
      have hδm := mul_le_mul_of_nonneg_left (hm y) hδ.le
      change _ + δ*(Q y).trace ≤ _
      linarith
  obtain ⟨ρ,H,hρ,htρ,hH,hpair,hbit'⟩ := states_of_domination Q T D hD hQ hT hdomD
    ((q:ℝ)*e+δ*m) hε htr hbit
  exact nearly_perfect_bit_tests ρ H hρ htρ hH hpair _ hε hsmall hbit'

end PerfectMatchingPSD

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.CellDecoder ----
namespace OAI

namespace MatchingInterpolation
open MatchingSmoothing PerfectMatchingPSD Matrix
open scoped BigOperators MatrixOrder
attribute [local instance] Classical.propDecidable

lemma cell_trace_value {s q r : ℕ}
    (Q : (Fin q → Bool) → Matrix (Fin r) (Fin r) ℝ)
    (B : Pairing (GlobalVertices s q) → Matrix (Fin r) (Fin r) ℝ)
    (hpair : ∀ y M, (Q y*B M).trace = tableCoordinate (globalCutColor y) (true,false) M-1)
    (y : Fin q → Bool) (i : Fin q) (x : Point)
    (hx : ∃ M : Pairing (TripleVertices s), crossVector threeColor M=x) :
    (Q y*cellMatrix i B x).trace = cutValue (y i) x := by
  have : Nonempty (Pairing (Fin s × Bool)) := ⟨standardPairing⟩
  rw [trace_cellMatrix]
  apply cellAverage_const i _ x _ hx
  intro M hM N
  rw [hpair, extendLocal_cut, hM]
  rfl

lemma cutValue_p (b : Bool) : cutValue b (origin+dirP) = 0 := by
  cases b <;> norm_num [cutValue, origin, dirP, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
lemma cutValue_star (b : Bool) : cutValue b (origin+dirStar) = 2 := by
  cases b <;> norm_num [cutValue, origin, dirStar, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
lemma cutValue_bit (b : Bool) : cutValue b (if b then origin+dirB else origin+dirA) = 2 := by
  cases b <;> norm_num [cutValue, origin, dirA, dirB, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

lemma cutValue_grid {d : ℕ} {L : ℝ} (hL : 0 ≤ L) (g : GridIndex d) (b : Bool) :
    cutValue b (scaledNode L g) ≤ 2*(d:ℝ)*L := by
  have hk (a : Fin 3) : (g a : ℝ) ≤ (d:ℝ) := by exact_mod_cast (Nat.le_of_lt_succ (g a).isLt)
  have h0 := mul_le_mul_of_nonneg_left (hk 0) hL
  have h1 := mul_le_mul_of_nonneg_left (hk 1) hL
  have h2 := mul_le_mul_of_nonneg_left (hk 2) hL
  cases b <;> norm_num [cutValue, scaledNode, origin, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] <;> nlinarith

lemma origin_star_eq : origin+dirStar = (![3,0,0] : Point) := by
  ext a
  fin_cases a <;> norm_num [origin, dirStar]

lemma weightMass_bound (d : ℕ) : ∃ c : ℝ, 0 < c ∧ ∀ L : ℝ, 1 ≤ L →
    weightMass d L ≤ c/L^2 := by
  obtain ⟨c,hc,hbound⟩ := weights_bound d
  refine ⟨(Fintype.card (GridIndex d) : ℝ)*c, mul_pos (by positivity) hc, ?_⟩
  intro L hL
  have he := Finset.sum_le_sum (s := Finset.univ) (fun g _ => hbound L hL g)
  simpa only [weightMass, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_assoc] using he

lemma cell_decoder {s q l r d : ℕ} (hs : 1 ≤ s) (hq : 1 ≤ q) (hsl : 2*l*d ≤ s)
    (Q : (Fin q → Bool) → Matrix (Fin r) (Fin r) ℝ)
    (B : Pairing (GlobalVertices s q) → Matrix (Fin r) (Fin r) ℝ)
    (hQ : ∀ y, (Q y).PosSemidef) (hB : ∀ M, (B M).PosSemidef)
    (hpair : ∀ y M, (Q y*B M).trace = tableCoordinate (globalCutColor y) (true,false) M-1)
    (P : Fin q → Fin r → Fin r → Point → ℝ)
    (hP : ∀ i u v, P i u v ∈ lowDegree coord d)
    {η m δ : ℝ} (hη : 0 ≤ η) (hδ : 0 < δ) (hl : 0 < l)
    (hm : ∀ y, (Q y).trace ≤ m)
    (happrox : ∀ i u v t, |cellMatrix i B (samplePoint d (2*l) t) u v-
      P i u v (samplePoint d (2*l) t)| ≤ η)
    (hε : 0 ≤ (q:ℝ)*(weightMass d (2*l)*(2*d*(2*l))+
      (r:ℝ)*(6+weightMass d (2*l))*η*m)+δ*m)
    (hsmall : (q:ℝ)*Real.sqrt ((q:ℝ)*(weightMass d (2*l)*(2*d*(2*l))+
      (r:ℝ)*(6+weightMass d (2*l))*η*m)+δ*m) ≤ 1/4) :
    (2:ℝ)^q/2 ≤ r := by
  let L : ℝ := 2*l
  have hL : 0 < L := by dsimp [L]; positivity
  let C := fun i => cellMatrix i B
  have hC (i : Fin q) (x : Point) : (C i x).PosSemidef := cellMatrix_psd i B hB x
  have hsamp (y : Fin q → Bool) (i : Fin q) (t : SampleIndex d) :
      (Q y*C i (samplePoint d L t)).trace = cutValue (y i) (samplePoint d L t) :=
    cell_trace_value Q B hpair y i _ (sample_witness hs hsl t)
  have hfive (y : Fin q → Bool) (i : Fin q) (j : Fin 5) :
      (Q y*C i (specialPoint j)).trace = cutValue (y i) (specialPoint j) := hsamp y i (.inl j)
  have hp (y : Fin q → Bool) (i : Fin q) : (Q y*C i (origin+dirP)).trace=0 :=
    (hfive y i 1).trans (cutValue_p _)
  have hstar (y : Fin q → Bool) (i : Fin q) : (Q y*C i (origin+dirStar)).trace=2 :=
    (hfive y i 2).trans (cutValue_star _)
  have hgrid (y : Fin q → Bool) (i : Fin q) (g : GridIndex d) :
      (Q y*C i (scaledNode L g)).trace ≤ 2*(d:ℝ)*L :=
    (hsamp y i (.inr g)).le.trans (cutValue_grid hL.le g (y i))
  have hEex (i : Fin q) := interpolation_matrix_domination d (C i) (hC i) (P i) (hP i)
    hL.ne' hη (fun j u v => happrox i u v (.inl j)) (fun g u v => happrox i u v (.inr g))
  choose E hE hdom hEb using hEex
  let i₀ : Fin q := ⟨0,by omega⟩
  let S := C i₀ (origin+dirStar)
  have hcommon (i : Fin q) : C i (origin+dirStar)=S := by
    dsimp only [S,C]
    rw [origin_star_eq]
    exact cellMatrix_star i i₀ B 3
  let T := fun i (b : Bool) => if b then C i (origin+dirB) else C i (origin+dirA)
  have hT (i : Fin q) (b : Bool) : (T i b).PosSemidef := by
    cases b <;> exact hC i _
  have hTdom (i : Fin q) : T i false+T i true ≤ S+(2:ℝ) • C i (origin+dirP)+E i := by
    change C i (origin+dirA)+C i (origin+dirB) ≤ S+(2:ℝ) • C i (origin+dirP)+E i
    rw [← hcommon i]
    exact hdom i
  have hbit (y : Fin q → Bool) (i : Fin q) : (Q y*T i (y i)).trace=2 := by
    cases hy : y i
    · exact (hfive y i 3).trans (by rw [hy]; exact cutValue_bit false)
    · exact (hfive y i 4).trans (by rw [hy]; exact cutValue_bit true)
  have he (y : Fin q → Bool) (i : Fin q) : (Q y*E i).trace ≤
      weightMass d L*(2*(d:ℝ)*L)+(r:ℝ)*(6+weightMass d L)*η*m := by
    simpa only [Fintype.card_fin] using hEb i (Q y) m (2*(d:ℝ)*L) (hm y) (hgrid y i)
  simpa only [Fintype.card_fin] using domination_decoder Q T (fun i => C i (origin+dirP)) E S hQ hT
    (fun i => hC i _) hE (hC i₀ _) hTdom hp (fun y => hstar y i₀) hbit hδ hm he hε hsmall

end MatchingInterpolation

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.CellLowerBound ----
namespace OAI

namespace MatchingInterpolation
open MatchingSmoothing PerfectMatchingPSD Matrix
open scoped BigOperators MatrixOrder

lemma interpolation_trace_error_bound (d : ℕ) {c L r η m : ℝ}
    (hc : 0 ≤ c) (hL : 1 ≤ L)
    (hw : weightMass d L ≤ c/L^2) (hnorm : r*η*m ≤ 1/L) :
    weightMass d L*(2*(d:ℝ)*L)+r*(6+weightMass d L)*η*m ≤
      ((2*(d:ℝ)+1)*c+6)/L := by
  have hLp : 0 < L := by linarith
  have hwc : weightMass d L ≤ c := by
    apply hw.trans
    exact (div_le_self hc (by nlinarith : 1 ≤ L^2))
  have h1 := mul_le_mul_of_nonneg_right hw (show 0 ≤ 2*(d:ℝ)*L by positivity)
  have h2 := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ 6+weightMass d L by linarith [weightMass_nonneg d L])
  have h3 := mul_le_mul_of_nonneg_right (show 6+weightMass d L ≤ 6+c by linarith) (show 0 ≤ 1/L by positivity)
  calc
    _ = weightMass d L*(2*(d:ℝ)*L)+(6+weightMass d L)*(r*η*m) := by ring
    _ ≤ (c/L^2)*(2*(d:ℝ)*L)+(6+c)*(1/L) := add_le_add h1 (h2.trans h3)
    _ = _ := by field_simp; ring

lemma sqrt_error_small {q D L ε : ℝ} (hq : 0 ≤ q) (hL : 0 < L) (hε : 0 ≤ ε)
    (he : ε ≤ (q*D+1)/L) (hn : 16*q^2*(q*D+1) ≤ L) :
    q*Real.sqrt ε ≤ 1/4 := by
  have heL : ε*L ≤ q*D+1 := (le_div_iff₀ hL).mp he
  have hmult := mul_le_mul_of_nonneg_left heL (show 0 ≤ 16*q^2 by positivity)
  have h16 : 16*q^2*ε ≤ 1 := by
    apply (mul_le_mul_iff_of_pos_right hL).mp
    nlinarith [hmult.trans hn]
  have hsq : (q*Real.sqrt ε)^2 = q^2*ε := by rw [mul_pow, Real.sq_sqrt hε]
  have hn0 : 0 ≤ q*Real.sqrt ε := mul_nonneg hq (Real.sqrt_nonneg _)
  nlinarith

lemma normalized_eta {r m L : ℝ} (hr : 0 < r) (hm : 0 < m) (hL : 0 < L) :
    r*(1/(r*m*L))*m = 1/L := by
  field_simp [hr.ne', hm.ne', hL.ne']

lemma conditional_cell_lower_bound (K : ℕ) :
    ∃ d H : ℕ, 0 < d ∧ ∃ D : ℝ, 0 < D ∧
    ∀ s q l r : ℕ, H ≤ 3*s+1 → 1 ≤ s → 1 ≤ q → 2*l*d ≤ s → 1 ≤ l → 0 < r →
    ∀ m : ℝ, 0 < m →
    ∀ (Q : Equiv.Perm (GlobalVertices s q) → (Fin q → Bool) → Matrix (Fin r) (Fin r) ℝ)
      (B : Pairing (GlobalVertices s q) → Matrix (Fin r) (Fin r) ℝ),
      (∀ a y, (Q a y).PosSemidef) → (∀ M, (B M).PosSemidef) →
      (∀ a y, (Q a y).trace ≤ m) → (∀ M, (B M).trace ≤ (r:ℝ)) →
      (∀ a y M, (Q a y*B (Pairing.relabel a M)).trace =
        tableCoordinate (globalCutColor y) (true,false) M-1) →
      (q:ℝ)*r^4*(Fintype.card (SampleIndex d))*((2*(3*s+1):ℝ)^(2*K))⁻¹ ≤
        (1/((r:ℝ)*m*(2*l)))^2 →
      16*(q:ℝ)^2*((q:ℝ)*D+1) ≤ 2*l →
      (2:ℝ)^q/2 ≤ r := by
  obtain ⟨d,H,hd,hgood⟩ := good_cell_polynomials K
  obtain ⟨c,hc,hw⟩ := weightMass_bound d
  let D := (2*(d:ℝ)+1)*c+6
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨d,H,hd,D,hD,?_⟩
  intro s q l r hH hs hq hsl hl hr m hm Q B hQ hB htrQ htrB hpair hnum hn
  let L : ℝ := 2*l
  have hL : 1 ≤ L := by dsimp [L]; exact_mod_cast (by omega : 1 ≤ 2*l)
  have hLp : 0 < L := by linarith
  have hrp : 0 < (r:ℝ) := by exact_mod_cast hr
  let η := 1/((r:ℝ)*m*L)
  let δ := 1/(L*m)
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨a,P,hP,happrox⟩ := hgood s q l r hH hs hsl B hB htrB η hη hnum
  let e := weightMass d L*(2*(d:ℝ)*L)+(r:ℝ)*(6+weightMass d L)*η*m
  have hw0 := weightMass_nonneg d L
  have he0 : 0 ≤ e := by dsimp [e]; positivity
  have he : e ≤ D/L := interpolation_trace_error_bound d hc.le hL
    (hw L hL) (le_of_eq (normalized_eta hrp hm hLp))
  have hδm : δ*m=1/L := by dsimp [δ]; field_simp [hLp.ne', hm.ne']
  have hε : 0 ≤ (q:ℝ)*e+δ*m := by positivity
  have heps : (q:ℝ)*e+δ*m ≤ ((q:ℝ)*D+1)/L := by
    have heq := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg q)
    rw [hδm]
    calc
      _ ≤ (q:ℝ)*(D/L)+1/L := add_le_add heq (le_refl (1/L))
      _ = _ := by ring
  have hsmall := sqrt_error_small (Nat.cast_nonneg q) hLp hε heps hn
  exact cell_decoder hs hq hsl (Q a) (fun M => B (Pairing.relabel a M))
    (hQ a) (fun M => hB _) (hpair a) P hP hη hδ (by omega)
      (htrQ a) happrox hε hsmall

end MatchingInterpolation

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.FiniteFactorization ----
namespace OAI

universe u_1 u_2

namespace PerfectMatchingPSD

lemma endpoint_count {n : ℕ} (U : Finset (Fin n)) (M : PerfectMatching n) :
    (∑ e ∈ M.1, ((if e.1.1 ∈ U then 1 else 0) +
      (if e.1.2 ∈ U then 1 else 0) : ℕ)) = U.card := by
  classical
  have pair_count (e : Edge n) :
      (∑ v ∈ U, (if e.1.1 = v ∨ e.1.2 = v then 1 else 0 : ℕ)) =
        (if e.1.1 ∈ U then 1 else 0) + (if e.1.2 ∈ U then 1 else 0) := by
    have pointwise (v : Fin n) :
        (if e.1.1 = v ∨ e.1.2 = v then 1 else 0 : ℕ) =
          (if e.1.1 = v then 1 else 0) + (if e.1.2 = v then 1 else 0) := by
      have hne : e.1.1 ≠ e.1.2 := ne_of_lt e.2
      by_cases h₁ : e.1.1 = v <;> by_cases h₂ : e.1.2 = v <;> simp_all
    simp_rw [pointwise]
    simp [Finset.sum_add_distrib]
  calc
    _ = ∑ e ∈ M.1, ∑ v ∈ U,
        (if e.1.1 = v ∨ e.1.2 = v then 1 else 0 : ℕ) := by
      apply Finset.sum_congr rfl
      intro e _
      exact (pair_count e).symm
    _ = ∑ v ∈ U, ∑ e ∈ M.1,
        (if e.1.1 = v ∨ e.1.2 = v then 1 else 0 : ℕ) := Finset.sum_comm
    _ = ∑ v ∈ U, (M.1.filter fun e => e.1.1 = v ∨ e.1.2 = v).card := by
      simp only [Finset.sum_boole, Nat.cast_id]
    _ = U.card := by
      have hm : ∀ v : Fin n,
          (M.1.filter fun e => e.1.1 = v ∨ e.1.2 = v).card = 1 := M.2
      simp [hm]

lemma cut_degree_identity {n : ℕ} (U : Finset (Fin n)) (M : PerfectMatching n) :
    U.card = 2 * (M.1.filter fun e => e.1.1 ∈ U ∧ e.1.2 ∈ U).card +
      crossingCount U M := by
  classical
  rw [← endpoint_count U M]
  have term (e : Edge n) :
      ((if e.1.1 ∈ U then 1 else 0) + (if e.1.2 ∈ U then 1 else 0) : ℕ) =
        2 * (if e.1.1 ∈ U ∧ e.1.2 ∈ U then 1 else 0) +
          (if Crosses U e then 1 else 0) := by
    by_cases h₁ : e.1.1 ∈ U <;> by_cases h₂ : e.1.2 ∈ U <;>
      simp [h₁, h₂, Crosses]
  simp_rw [term]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_boole, Nat.cast_id, crossingCount]

lemma crossingCount_pos {n : ℕ} (U : OddCut n) (M : PerfectMatching n) :
    0 < crossingCount U.1 M := by
  obtain ⟨k, hk⟩ := U.2
  have h := cut_degree_identity U.1 M
  omega

lemma slack_nonneg {n : ℕ} (i : Row n) (M : PerfectMatching n) :
    0 ≤ slack i M := by
  classical
  rcases i with e | U
  · simp only [slack]
    split_ifs <;> norm_num
  · have h : 1 ≤ crossingCount U.1 M := crossingCount_pos U M
    have hr : (1 : ℝ) ≤ (crossingCount U.1 M : ℝ) := by exact_mod_cast h
    simpa only [slack, sub_nonneg] using hr

lemma exists_diagonal_factorization {I : Type u_1} {J : Type u_2} [Finite J]
    (S : I → J → ℝ) (hS : ∀ i j, 0 ≤ S i j) :
    ∃ r : ℕ, 0 < r ∧
      ∃ (A : I → Matrix (Fin r) (Fin r) ℝ)
        (B : J → Matrix (Fin r) (Fin r) ℝ),
        (∀ i, (A i).PosSemidef) ∧ (∀ j, (B j).PosSemidef) ∧
        ∀ i j, S i j = Matrix.trace (A i * B j) := by
  classical
  let : Fintype J := Fintype.ofFinite J
  let e := Fintype.equivFin (Option J)
  let a (i : I) (k : Option J) : ℝ := k.elim 0 (S i)
  let b (j : J) (k : Option J) : ℝ := if k = some j then 1 else 0
  refine ⟨Fintype.card (Option J), by simp,
    (fun i => (Matrix.diagonal (a i)).submatrix e.symm e.symm),
    (fun j => (Matrix.diagonal (b j)).submatrix e.symm e.symm), ?_, ?_, ?_⟩
  · intro i
    apply Matrix.PosSemidef.submatrix
    apply Matrix.PosSemidef.diagonal
    intro k
    cases k with
    | none => exact le_rfl
    | some j => exact hS i j
  · intro j
    apply Matrix.PosSemidef.submatrix
    apply Matrix.PosSemidef.diagonal
    intro k
    dsimp [b]
    split_ifs <;> norm_num
  · intro i j
    rw [Matrix.submatrix_mul_equiv, Matrix.diagonal_mul_diagonal,
      Matrix.submatrix_diagonal _ _ e.symm.injective, Matrix.trace_diagonal]
    dsimp only [Function.comp_def]
    rw [e.symm.sum_comp (fun k => a i k * b j k)]
    simp [a, b]

lemma factor_orders_nonempty (n : ℕ) :
    {r : ℕ | 0 < r ∧ HasFactorization n r}.Nonempty := by
  obtain ⟨r, hr, h⟩ := exists_diagonal_factorization (@slack n) slack_nonneg
  exact ⟨r, hr, h⟩

lemma psdRank_pos (n : ℕ) : 0 < psdRank n :=
  (Nat.sInf_mem (factor_orders_nonempty n)).1

lemma hasFactorization_psdRank (n : ℕ) : HasFactorization n (psdRank n) :=
  (Nat.sInf_mem (factor_orders_nonempty n)).2

lemma psdRank_le {n r : ℕ} (hr : 0 < r) (h : HasFactorization n r) :
    psdRank n ≤ r := Nat.sInf_le ⟨hr, h⟩

end PerfectMatchingPSD

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.AffineSlacks ----
namespace OAI

namespace PerfectMatchingPSD
open MatchingSmoothing Finset Matrix
open scoped BigOperators

lemma slackAffine_nonneg {n : ℕ} (i : Row n) {x : Edge n → ℝ}
    (hx : x ∈ matchingPolytope n) : 0 ≤ slackAffine i x := by
  have hc : Convex ℝ {x : Edge n → ℝ | 0 ≤ slackAffine i x} := by
    exact (convex_Ici (0 : ℝ)).affine_preimage (slackAffine i)
  apply convexHull_min _ hc hx
  rintro _ ⟨M, rfl⟩
  rw [Set.mem_ofPred_eq, slackAffine_vertex]
  exact slack_nonneg i M

end PerfectMatchingPSD

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.MatchingConversion ----
namespace OAI

namespace PerfectMatchingPSD
open MatchingSmoothing
attribute [local instance] Classical.propDecidable

lemma crossingCount_tableCoordinate {n : ℕ} (M : Pairing (Fin n)) (U : Finset (Fin n)) :
    (crossingCount U (fromPairing M) : ℝ) =
      tableCoordinate (fun v => decide (v ∈ U)) (true,false) M := by
  rw [crossingCount_fromPairing]
  simp [tableCoordinate, Fintype.card_subtype, Finset.sum_boole]

end PerfectMatchingPSD

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.TightMatchings ----
namespace OAI

namespace PerfectMatchingPSD
open MatchingSmoothing Finset Matrix
open scoped BigOperators

lemma oddCut_has_tight_matching {n : ℕ} (he : Even n) (U : OddCut n) :
    ∃ M : PerfectMatching n, slack (Sum.inr U) M = 0 := by
  classical
  have hu := U.2
  obtain ⟨a, ha⟩ := hu
  have hcomp : Odd (n - U.1.card) := by
    have hle : U.1.card ≤ n := by simpa using Finset.card_le_univ U.1
    rw [Nat.odd_iff]
    obtain ⟨k, hk⟩ := he
    omega
  obtain ⟨b, hb⟩ := hcomp
  let z : Fin n → Fin 3 := fun v => if v ∈ U.1 then 0 else 1
  let E : Fin 6 → ℕ := ![a, 1, 0, b, 0, 0]
  have hh : histogram z = endpointSizes E := by
    ext c
    fin_cases c
    · simp [histogram, z, endpointSizes, E, ← ha]
    · have hc : U.1ᶜ.card = n - U.1.card := by simp [Finset.card_compl]
      simp only [histogram, z, endpointSizes, E, Matrix.cons_val_one,
        Matrix.cons_val_zero]
      simp
      omega
    · simp [histogram, z, endpointSizes, E, ite_eq_iff]
  obtain ⟨M, hM⟩ := exists_pairing_of_endpoints z E hh
  refine ⟨fromPairing M, ?_⟩
  have hcross := hM 0
  have heq : (crossingCount U.1 (fromPairing M) : ℝ) = crossCoordinate z 0 M := by
    rw [crossingCount_fromPairing]
    simp [crossCoordinate, crossPair, tableCoordinate, z, Fintype.card_subtype,
      Finset.sum_boole]
  change (crossingCount U.1 (fromPairing M) : ℝ) - 1 = 0
  rw [heq, hcross]
  simp [E]

lemma edge_has_tight_matching {n : ℕ} (hn : 4 ≤ n) (he : Even n) (e : Edge n) :
    ∃ M : PerfectMatching n, slack (Sum.inl e) M = 0 := by
  classical
  obtain ⟨k, hk⟩ := he
  let f : (Fin k × Bool) ≃ Fin n := Fintype.equivOfCardEq (by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    omega)
  let P : Pairing (Fin n) := Pairing.transport f standardPairing
  by_cases hP : P.1 e.1.1 = e.1.2
  · have hcard : ({e.1.1, e.1.2} : Finset (Fin n)).card <
        (Finset.univ : Finset (Fin n)).card := by
      have hh := Finset.card_le_two (a := e.1.1) (b := e.1.2)
      simpa using lt_of_le_of_lt hh (show 2 < n by omega)
    obtain ⟨c, _, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    have hca : c ≠ e.1.1 := by simpa using (not_or.mp (by simpa using hc)).1
    have hcb : c ≠ e.1.2 := by simpa using (not_or.mp (by simpa using hc)).2
    let Q := Pairing.relabel (Equiv.swap e.1.2 c) P
    have hQ : Q.1 e.1.1 = c := by
      simp [Q, Equiv.swap_apply_of_ne_of_ne (ne_of_lt e.2) hca.symm, hP]
    refine ⟨fromPairing Q, ?_⟩
    simp [slack, mem_fromPairing, hQ, hcb]
  · refine ⟨fromPairing P, ?_⟩
    simp [slack, mem_fromPairing, hP]

lemma row_has_tight_matching {n : ℕ} (hn : 4 ≤ n) (he : Even n) (i : Row n) :
    ∃ M : PerfectMatching n, slack i M = 0 := by
  cases i with
  | inl e => exact edge_has_tight_matching hn he e
  | inr U => exact oddCut_has_tight_matching he U

end PerfectMatchingPSD

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.NormalizedFactors ----
namespace OAI

namespace PerfectMatchingPSD
open MatchingSmoothing Matrix
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma perfectMatching_nonempty {n : ℕ} (hn : Even n) : Nonempty (PerfectMatching n) := by
  classical
  obtain ⟨k,hk⟩ := hn
  let e : (Fin k × Bool) ≃ Fin n := Fintype.equivOfCardEq (by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    omega)
  exact ⟨fromPairing (Pairing.transport e standardPairing)⟩

lemma slack_le_vertices {n : ℕ} (hn : 1 ≤ n) (i : Row n) (M : PerfectMatching n) :
    slack i M ≤ (n:ℝ) := by
  rcases i with e | U
  · simp only [slack]
    split_ifs
    · exact_mod_cast hn
    · positivity
  · have hd := cut_degree_identity U.1 M
    have hcard : U.1.card ≤ n := by simpa using Finset.card_le_univ U.1
    have hc : crossingCount U.1 M ≤ n := by omega
    have hc' : (crossingCount U.1 M : ℝ) ≤ n := by exact_mod_cast hc
    change (crossingCount U.1 M : ℝ)-1 ≤ (n:ℝ)
    linarith

lemma normalized_factorization {n r : ℕ} (hn : Even n) (hnpos : 1 ≤ n)
    (hfac : HasFactorization n r) :
    ∃ (A : Row n → Matrix (Fin r) (Fin r) ℝ)
      (B : PerfectMatching n → Matrix (Fin r) (Fin r) ℝ),
      (∀ i, (A i).PosSemidef) ∧ (∀ M, (B M).PosSemidef) ∧
      (∀ i M, (A i*B M).trace = slack i M) ∧
      (∀ i, (A i).trace ≤ (n:ℝ)+1) ∧ (∀ M, (B M).trace ≤ (r:ℝ)) := by
  classical
  have := perfectMatching_nonempty hn
  rcases hfac with ⟨A,B,hA,hB,hpair⟩
  obtain ⟨A',B',hA',hB',hpair',htrA,htrB⟩ := exists_normalized_factors A B hA hB (n:ℝ)
    (fun i M => by rw [← hpair]; exact slack_le_vertices hnpos i M)
  exact ⟨A',B',hA',hB',fun i M => (hpair' i M).trans (hpair i M).symm,
    htrA,by simpa using htrB⟩

end PerfectMatchingPSD

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.AffineFactorization ----
namespace OAI

namespace PerfectMatchingPSD
open MatchingSmoothing Finset Matrix
open scoped BigOperators

theorem affineLift_hasFactorization {n r : ℕ} (hn : 4 ≤ n) (he : Even n)
    (h : HasAffineLift n r) : HasFactorization n r := by
  classical
  obtain ⟨L, T, hT⟩ := h
  have hvertex (M : PerfectMatching n) : ∃ X : Matrix (Fin r) (Fin r) ℝ,
      X ∈ L ∧ X.PosSemidef ∧ T X = matchingPoint M := by
    have hm : matchingPoint M ∈ matchingPolytope n :=
      subset_convexHull ℝ _ (Set.mem_range_self M)
    rw [← hT] at hm
    obtain ⟨X, hX, heq⟩ := hm
    exact ⟨X, hX.1, hX.2, heq⟩
  choose B hBL hB hBT using hvertex
  have hrow (i : Row n) : ∃ A : Matrix (Fin r) (Fin r) ℝ,
      A.PosSemidef ∧ ∀ M, (A * B M).trace = slack i M := by
    obtain ⟨M₀, hzero⟩ := row_has_tight_matching hn he i
    have hnonneg (X : Matrix (Fin r) (Fin r) ℝ) (hXL : X ∈ L)
        (hXP : X.PosSemidef) : 0 ≤ ((slackAffine i).comp T) X := by
      apply slackAffine_nonneg
      rw [← hT]
      exact ⟨X, ⟨hXL, hXP⟩, rfl⟩
    have hz : ((slackAffine i).comp T) (B M₀) = 0 := by
      simpa only [AffineMap.comp_apply, hBT, slackAffine_vertex] using hzero
    obtain ⟨A, hA, hAB⟩ := AffinePSD.affine_slack_certificate L B hB hBL
      ((slackAffine i).comp T) hnonneg M₀ hz
    refine ⟨A, hA, fun M => ?_⟩
    simpa only [AffineMap.comp_apply, hBT, slackAffine_vertex] using hAB M
  choose A hA hAB using hrow
  exact ⟨A, B, hA, hB, fun i M => (hAB i M).symm⟩

lemma factorization_order_pos {n r : ℕ} (hn : 1 ≤ n) (he : Even n)
    (h : HasFactorization n r) : 0 < r := by
  classical
  by_contra hr
  have hr0 : r = 0 := by omega
  subst r
  obtain ⟨M⟩ := perfectMatching_nonempty he
  let v : Fin n := ⟨0, by omega⟩
  have hc := M.2 v
  obtain ⟨e, heq⟩ := Finset.card_eq_one.mp hc
  have heM : e ∈ M.1 := (Finset.mem_filter.mp (heq.symm ▸ Finset.mem_singleton_self e)).1
  obtain ⟨A, B, hA, hB, hf⟩ := h
  have hz := hf (Sum.inl e) M
  simp [slack, heM, Matrix.trace] at hz

end PerfectMatchingPSD

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.Padding ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace PerfectMatchingPSD
open MatchingSmoothing Matrix
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma colorCut_slack {n : ℕ} {V : Type u_2} [Fintype V]
    (e : V ≃ Fin n) (z : V → Bool) (hz : Odd (Fintype.card {v // z v = true}))
    (M : Pairing V) :
    slack (Sum.inr (colorCut e z hz)) (fromPairing (Pairing.transport e M)) =
      tableCoordinate z (true,false) M - 1 := by
  classical
  rw [slack, crossingCount_tableCoordinate, tableCoordinate_transport]
  congr 2
  funext v
  simp [colorCut]

lemma true_card_comp_equiv {V : Type u_3} {W : Type u_4} [Fintype V] [Fintype W]
    (z : V → Bool) (e : W ≃ V) :
    Fintype.card {w // z (e w) = true} = Fintype.card {v // z v = true} :=
  Fintype.card_congr (Equiv.subtypeEquiv e (fun _ => Iff.rfl))

lemma true_card_sum_false {V : Type u_5} {W : Type u_6} [Fintype V] [Fintype W] (z : V → Bool) :
    Fintype.card {v : V ⊕ W // Sum.elim z (fun _ => false) v = true} =
      Fintype.card {v : V // z v = true} := by
  classical
  let e : {v : V ⊕ W // Sum.elim z (fun _ => false) v = true} ≃ {v : V // z v = true} :=
    { toFun := fun v => match v with
        | ⟨Sum.inl a,h⟩ => ⟨a,h⟩
        | ⟨Sum.inr _,h⟩ => nomatch h
      invFun := fun v => ⟨Sum.inl v.1,v.2⟩
      left_inv := by
        rintro ⟨v,h⟩
        cases v with
        | inl v => rfl
        | inr v => exact False.elim (Bool.false_ne_true h)
      right_inv := by intro v; rfl }
  exact Fintype.card_congr e

lemma tableCoordinate_false {V : Type u_7} [Fintype V] (M : Pairing V) :
    tableCoordinate (fun _ : V => false) (true,false) M = 0 := by
  simp [tableCoordinate]

lemma global_factors_of_factorization {n r s q : ℕ} (hn : Even n) (hnpos : 1 ≤ n)
    (hfac : HasFactorization n r) {W : Type} [Fintype W]
    (e : (GlobalVertices s q ⊕ W) ≃ Fin n) (MW : Pairing W) :
    ∃ (Q : Equiv.Perm (GlobalVertices s q) → (Fin q → Bool) → Matrix (Fin r) (Fin r) ℝ)
      (B : Pairing (GlobalVertices s q) → Matrix (Fin r) (Fin r) ℝ),
      (∀ a y, (Q a y).PosSemidef) ∧ (∀ M, (B M).PosSemidef) ∧
      (∀ a y, (Q a y).trace ≤ (n:ℝ)+1) ∧ (∀ M, (B M).trace ≤ (r:ℝ)) ∧
      ∀ a y M, (Q a y * B (Pairing.relabel a M)).trace =
        tableCoordinate (globalCutColor y) (true,false) M - 1 := by
  classical
  obtain ⟨A,B,hA,hB,hpair,htrA,htrB⟩ := normalized_factorization hn hnpos hfac
  let z (a : Equiv.Perm (GlobalVertices s q)) (y : Fin q → Bool) : GlobalVertices s q ⊕ W → Bool :=
    Sum.elim (globalCutColor y ∘ a.symm) (fun _ => false)
  have hz (a : Equiv.Perm (GlobalVertices s q)) (y : Fin q → Bool) :
      Odd (Fintype.card {v // z a y v = true}) := by
    rw [true_card_sum_false]
    change Odd (Fintype.card {v // globalCutColor y (a.symm v) = true})
    rw [true_card_comp_equiv]
    exact globalCutColor_odd s q y
  let U (a : Equiv.Perm (GlobalVertices s q)) (y : Fin q → Bool) := colorCut e (z a y) (hz a y)
  refine ⟨fun a y => A (Sum.inr (U a y)),
    fun M => B (fromPairing (Pairing.transport e (Pairing.sum M MW))),
    fun a y => hA _, fun M => hB _, fun a y => htrA _, fun M => htrB _, ?_⟩
  intro a y M
  rw [hpair, colorCut_slack, tableCoordinate_sum, tableCoordinate_false, add_zero]
  congr 1
  rw [← Pairing.transport_perm, tableCoordinate_transport]
  congr 1
  ext v
  simp

end PerfectMatchingPSD

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.Parameters ----
namespace OAI

namespace PerfectMatchingPSD
open MatchingSmoothing MatchingInterpolation Matrix Filter Asymptotics
open scoped BigOperators MatrixOrder

lemma index_le_vertexSize (d t : ℕ) : t ≤ vertexSize d t := by
  have ht : t ≤ t^4 := Nat.le_pow (by decide)
  have hc : 1 ≤ 8*(d+1)*(t+2) := by
    have : 0 < 8*(d+1)*(t+2) := by positivity
    omega
  calc
    t ≤ t^4 := ht
    _ ≤ (8*(d+1)*(t+2))*t^4 := by simpa only [one_mul] using Nat.mul_le_mul_right (t^4) hc
    _ ≤ vertexSize d t := by dsimp [vertexSize, blockSize]; nlinarith

lemma vertexSize_succ_bound (d t : ℕ) (ht : 1 ≤ t) :
    vertexSize d (t+1) ≤ 1024*(d+1)*t^5 := by
  have hp : 1 ≤ (d+1)*t^5 := by
    have : 0 < (d+1)*t^5 := by positivity
    omega
  calc
    _ = 8*(d+1)*(t+1)^4*(t+3)+2 := by dsimp [vertexSize, blockSize]; ring
    _ ≤ 8*(d+1)*(2*t)^4*(4*t)+2 := by gcongr <;> omega
    _ = 512*(d+1)*t^5+2 := by ring
    _ ≤ _ := by nlinarith

lemma vertexSize_succ_le_pow6 (d t : ℕ) (ht : 1 ≤ t) (hd : 1024*(d+1) ≤ t) :
    vertexSize d (t+1) ≤ t^6 := by
  calc
    _ ≤ 1024*(d+1)*t^5 := vertexSize_succ_bound d t ht
    _ ≤ t*t^5 := Nat.mul_le_mul_right _ hd
    _ = _ := by ring

lemma bracket_vertexSize (d T n : ℕ) (hn : vertexSize d T ≤ n) :
    ∃ t : ℕ, T ≤ t ∧ vertexSize d t ≤ n ∧ n < vertexSize d (t+1) := by
  classical
  let P := fun t => vertexSize d t ≤ n
  let t := Nat.findGreatest P n
  have hT : T ≤ n := (index_le_vertexSize d T).trans hn
  refine ⟨t, Nat.le_findGreatest (P := P) hT hn, Nat.findGreatest_spec (P := P) hT hn, ?_⟩
  by_contra h
  have hnext : P (t+1) := le_of_not_gt h
  have htn : t+1 ≤ n := (index_le_vertexSize d (t+1)).trans hnext
  exact (Nat.findGreatest_eq_iff.mp (show Nat.findGreatest P n=t from rfl)).2.2
    (Nat.lt_succ_self t) htn hnext

lemma exists_padded_global_equiv {n s q : ℕ} (hn : Even n) (hle : 2*s*(q+2)+2 ≤ n) :
    ∃ k : ℕ, Nonempty ((GlobalVertices s q ⊕ (Fin k × Bool)) ≃ Fin n) := by
  have hg : Even (2*s*(q+2)+2) := ⟨s*(q+2)+1, by ring⟩
  have hd : Even (n-(2*s*(q+2)+2)) := (Nat.even_sub hle).mpr ⟨fun _ => hg, fun _ => hn⟩
  obtain ⟨k,hk⟩ := hd
  refine ⟨k, ⟨Fintype.equivOfCardEq ?_⟩⟩
  rw [Fintype.card_sum, globalVertices_card]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  omega

lemma eventually_pow_lt_half_exp (p : ℕ) :
    ∀ᶠ t : ℕ in atTop, (t:ℝ)^p < (2:ℝ)^t/2 := by
  have ho := isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) p (by norm_num : 1 < (2:ℝ))
  have hb := ho.bound (by norm_num : (0:ℝ) < 1/4)
  filter_upwards [hb] with t ht
  have ht' : (t:ℝ)^p ≤ (1/4)*(2:ℝ)^t := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (show (0:ℝ) ≤ (t:ℝ)^p by positivity),
      abs_of_pos (pow_pos (by norm_num : (0:ℝ)<2) _)] using ht
  calc
    _ ≤ (1/4)*(2:ℝ)^t := ht'
    _ < _ := by nlinarith [pow_pos (by norm_num : (0:ℝ)<2) t]

end PerfectMatchingPSD

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.NumericalBounds ----
namespace OAI

namespace PerfectMatchingPSD
open MatchingSmoothing MatchingInterpolation Matrix
open scoped BigOperators MatrixOrder

lemma blockSize_ge (d t : ℕ) : t^4 ≤ blockSize d t := by
  dsimp [blockSize]
  simpa only [one_mul] using Nat.mul_le_mul_right (t^4) (show 1 ≤ 4*(d+1) by omega)

lemma blockSize_grid (d t : ℕ) : 2*t^4*d ≤ blockSize d t := by
  dsimp [blockSize]
  calc
    2*t^4*d = (2*d)*t^4 := by ring
    _ ≤ 4*(d+1)*t^4 := Nat.mul_le_mul_right _ (by omega)

lemma selection_of_cleared {q r T m L b : ℝ} (hb : 0 < b) (hc : 0 < r*m*L)
    (hnum : q*r^6*T*m^2*L^2 ≤ b) :
    q*r^4*T*b⁻¹ ≤ (1/(r*m*L))^2 := by
  rw [← div_eq_mul_inv, div_pow, one_pow]
  apply (div_le_div_iff₀ hb (sq_pos_of_pos hc)).mpr
  calc
    _ = q*r^6*T*m^2*L^2 := by ring
    _ ≤ b := hnum
    _ = _ := by ring

lemma numerical_selection (p d t r n T : ℕ) (ht : 2 ≤ t) (hr : 0 < r)
    (hn : n ≤ t^6) (hT : T ≤ t) (hrn : (r:ℝ) ≤ (n:ℝ)^p) :
    (t:ℝ)*r^4*T*((2*(3*(blockSize d t:ℝ)+1))^(2*(10*(p+1))))⁻¹ ≤
      (1/((r:ℝ)*((n:ℝ)+1)*(2*(t:ℝ)^4)))^2 := by
  have ht2 : (2:ℝ) ≤ t := by exact_mod_cast ht
  have ht1 : (1:ℝ) ≤ t := by linarith
  have ht0 : (0:ℝ) ≤ t := Nat.cast_nonneg t
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
  have hn6 : (n:ℝ) ≤ (t:ℝ)^6 := by exact_mod_cast hn
  have hrp : (r:ℝ) ≤ (t:ℝ)^(6*p) := by
    simpa only [pow_mul] using hrn.trans (pow_le_pow_left₀ (Nat.cast_nonneg n) hn6 p)
  have hm : (n:ℝ)+1 ≤ (t:ℝ)^7 := by
    have h6 : (1:ℝ) ≤ (t:ℝ)^6 := one_le_pow₀ ht1
    calc
      _ ≤ (t:ℝ)^6+(t:ℝ)^6 := add_le_add hn6 h6
      _ = 2*(t:ℝ)^6 := by ring
      _ ≤ (t:ℝ)*(t:ℝ)^6 := mul_le_mul_of_nonneg_right ht2 (pow_nonneg ht0 _)
      _ = _ := by ring
  have hL : 2*(t:ℝ)^4 ≤ (t:ℝ)^5 := by
    calc
      _ ≤ (t:ℝ)*(t:ℝ)^4 := mul_le_mul_of_nonneg_right ht2 (pow_nonneg ht0 _)
      _ = _ := by ring
  have hTr : (T:ℝ) ≤ t := by exact_mod_cast hT
  have hbase : (t:ℝ)^4 ≤ 2*(3*(blockSize d t:ℝ)+1) := by
    have hs : (t:ℝ)^4 ≤ (blockSize d t:ℝ) := by exact_mod_cast blockSize_ge d t
    have hs0 : (0:ℝ) ≤ (blockSize d t:ℝ) := Nat.cast_nonneg _
    linarith
  have hb : 0 < (2*(3*(blockSize d t:ℝ)+1))^(2*(10*(p+1))) := by positivity
  apply selection_of_cleared hb (by positivity)
  calc
    _ ≤ (t:ℝ)*((t:ℝ)^(6*p))^6*(t:ℝ)*((t:ℝ)^7)^2*((t:ℝ)^5)^2 := by gcongr
    _ = (t:ℝ)^(36*p+26) := by
      have he : 36*p+26 = 1+(6*p)*6+1+7*2+5*2 := by omega
      rw [he]
      simp only [pow_add, pow_mul, pow_one]
    _ ≤ (t:ℝ)^(8*(10*(p+1))) := pow_le_pow_right₀ ht1 (by omega)
    _ = ((t:ℝ)^4)^(2*(10*(p+1))) := by rw [← pow_mul]; congr 1; omega
    _ ≤ _ := pow_le_pow_left₀ (pow_nonneg ht0 _) hbase _

lemma numerical_smallness (D : ℝ) (t : ℕ) (ht : 1 ≤ t) (hD : 8*(D+1) ≤ (t:ℝ)) :
    16*(t:ℝ)^2*((t:ℝ)*D+1) ≤ 2*(t:ℝ)^4 := by
  have ht1 : (1:ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0:ℝ) ≤ t := Nat.cast_nonneg t
  calc
    _ ≤ 16*(t:ℝ)^2*((t:ℝ)*(D+1)) := by gcongr; linarith
    _ = 2*(t:ℝ)^3*(8*(D+1)) := by ring
    _ ≤ 2*(t:ℝ)^3*(t:ℝ) := mul_le_mul_of_nonneg_left hD (by positivity)
    _ = _ := by ring

end PerfectMatchingPSD

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.Main ----
namespace OAI

namespace PerfectMatchingPSD
open MatchingSmoothing MatchingInterpolation Matrix Filter Asymptotics
open scoped BigOperators MatrixOrder

lemma main_nat (p : ℕ) : ∃ n₀ : ℕ, 4 ≤ n₀ ∧
    ∀ n : ℕ, n₀ ≤ n → Even n → (n:ℝ)^p < (psdRank n:ℝ) := by
  classical
  obtain ⟨d,H,hd,D,hD,hdecode⟩ := conditional_cell_lower_bound (10*(p+1))
  obtain ⟨Te,hTe⟩ := eventually_atTop.mp (eventually_pow_lt_half_exp (6*p))
  let T := 2+H+1024*(d+1)+Fintype.card (SampleIndex d)+⌈8*(D+1)⌉₊+Te
  refine ⟨vertexSize d T+4, by omega, ?_⟩
  intro n hn hneven
  obtain ⟨t,ht,hleft,hright⟩ := bracket_vertexSize d T n (by omega)
  dsimp only [T] at ht
  have ht2 : 2 ≤ t := by omega
  have ht1 : 1 ≤ t := by omega
  have hHt : H ≤ t := by omega
  have hdt : 1024*(d+1) ≤ t := by omega
  have hTt : Fintype.card (SampleIndex d) ≤ t := by omega
  have hDt : 8*(D+1) ≤ (t:ℝ) :=
    (Nat.le_ceil (8*(D+1))).trans (by exact_mod_cast (show ⌈8*(D+1)⌉₊ ≤ t by omega))
  have htet : Te ≤ t := by omega
  have hn6 : n ≤ t^6 := hright.le.trans (vertexSize_succ_le_pow6 d t ht1 hdt)
  have hl : 1 ≤ t^4 := one_le_pow₀ ht1
  have hs : 1 ≤ blockSize d t := hl.trans (blockSize_ge d t)
  have hH : H ≤ 3*blockSize d t+1 := by
    have hts : t ≤ blockSize d t := (Nat.le_pow (by decide : 0 < 4)).trans (blockSize_ge d t)
    omega
  by_contra hnot
  have hrn : (psdRank n:ℝ) ≤ (n:ℝ)^p := le_of_not_gt hnot
  obtain ⟨k,⟨e⟩⟩ := exists_padded_global_equiv hneven hleft
  obtain ⟨Q,B,hQ,hB,htrQ,htrB,hpair⟩ := global_factors_of_factorization
    hneven (by omega : 1 ≤ n) (hasFactorization_psdRank n) e (standardPairing (H := Fin k))
  have hsel : (t:ℝ)*(psdRank n)^4*(Fintype.card (SampleIndex d))*
      ((2*(3*(blockSize d t:ℝ)+1))^(2*(10*(p+1))))⁻¹ ≤
      (1/((psdRank n:ℝ)*((n:ℝ)+1)*(2*(t^4:ℕ))))^2 := by
    simpa only [Nat.cast_pow] using numerical_selection p d t (psdRank n) n
      (Fintype.card (SampleIndex d)) ht2 (psdRank_pos n) hn6 hTt hrn
  have hsmall : 16*(t:ℝ)^2*((t:ℝ)*D+1) ≤ 2*(t^4:ℕ) := by
    simpa only [Nat.cast_pow] using numerical_smallness D t ht1 hDt
  have hlower : (2:ℝ)^t/2 ≤ (psdRank n:ℝ) :=
    hdecode (blockSize d t) t (t^4) (psdRank n) hH hs ht1 (blockSize_grid d t) hl
      (psdRank_pos n) ((n:ℝ)+1) (by positivity) Q B hQ hB htrQ htrB hpair hsel hsmall
  have hn6r : (n:ℝ) ≤ (t:ℝ)^6 := by exact_mod_cast hn6
  have hpow : (n:ℝ)^p ≤ (t:ℝ)^(6*p) := by
    simpa only [pow_mul] using pow_le_pow_left₀ (Nat.cast_nonneg n) hn6r p
  exact (not_lt_of_ge hlower) ((hrn.trans hpow).trans_lt (hTe t htet))

theorem main : MainClaim := by
  intro C _hC
  obtain ⟨n₀,hn₀,hmain⟩ := main_nat ⌈C⌉₊
  refine ⟨n₀,hn₀,?_⟩
  intro n hn heven
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hpow := Real.rpow_le_rpow_of_exponent_le hn1 (Nat.le_ceil C)
  rw [Real.rpow_natCast] at hpow
  exact hpow.trans_lt (hmain n hn heven)

end PerfectMatchingPSD

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.AffineLift ----
namespace OAI

namespace PerfectMatchingPSD
open MatchingSmoothing Finset Matrix
open scoped BigOperators

theorem affine_lift_lower_bound :
    ∀ C : ℝ, 0 < C → ∃ n₀ : ℕ, 4 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → Even n → ∀ r : ℕ,
        HasAffineLift n r → (n : ℝ) ^ C < (r : ℝ) := by
  intro C hC
  obtain ⟨n₀, hn₀, hmain⟩ := main C hC
  refine ⟨n₀, hn₀, ?_⟩
  intro n hn he r h
  have hn4 : 4 ≤ n := hn₀.trans hn
  have hf := affineLift_hasFactorization hn4 he h
  have hr := factorization_order_pos (by omega) he hf
  exact (hmain n hn he).trans_le (by exact_mod_cast psdRank_le hr hf)

end PerfectMatchingPSD

end OAI

-- ---- mission target ----
open OAI OAI.PerfectMatchingPSD
open MatchingSmoothing Finset Matrix
open scoped BigOperators

namespace OAI
namespace PerfectMatchingPSD
theorem _root_.solution :
    ∀ C : ℝ, 0 < C → ∃ n₀ : ℕ, 4 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → Even n → ∀ r : ℕ,
        HasAffineLift n r → (n : ℝ) ^ C < (r : ℝ) := by
  first
    | exact OAI.PerfectMatchingPSD.affine_lift_lower_bound
    | (apply OAI.PerfectMatchingPSD.affine_lift_lower_bound <;> assumption)
    | (intros; apply OAI.PerfectMatchingPSD.affine_lift_lower_bound <;> assumption)
end PerfectMatchingPSD
end OAI

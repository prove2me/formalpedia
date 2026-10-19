-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Nibble.nibble_iteration
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:51:59.349673+00:00
-- url     : https://prove2.me/submissions/ab125e8e-6f85-4059-9065-254b2800a59a

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Nibble.lean:L772-L919
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Nibble.nibble_iteration. The node keeps its source
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
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Nibble_one_round

-- ---- from OAI.Analysis.Littlewood.Nibble ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uI uE uV

namespace AsymptoticallyMinimalLittlewood
namespace Nibble
open scoped BigOperators
open Finset
section SetUnions
variable {I : Type uI} {E : Type uE} [DecidableEq I] [DecidableEq E]

end SetUnions

section Hypergraph
variable {V : Type uV} {E : Type uE} [DecidableEq V] [Fintype E] [DecidableEq E]

omit [Fintype E] [DecidableEq E] in
lemma incident_mono {S T : Finset E} (h : S ⊆ T) (A : E → Finset V) (v : V) :
    incident S A v ⊆ incident T A v := by
  intro e he
  obtain ⟨he, hv⟩ := mem_incident S A v e |>.mp he
  exact mem_incident T A v e |>.mpr ⟨h he, hv⟩

namespace PackingState

omit [Fintype E] in
lemma compose_waste {U : Finset V} {S : Finset E} {A : E → Finset V}
    (P : PackingState U S A) (Q : PackingState P.vertices P.edges A) :
    ((U \ ((P.compose Q).vertices ∪ (P.compose Q).chosen.biUnion A)).card : ℝ) ≤
      (U \ (P.vertices ∪ P.chosen.biUnion A)).card +
      (P.vertices \ (Q.vertices ∪ Q.chosen.biUnion A)).card := by
  have hsub : U \ ((P.compose Q).vertices ∪ (P.compose Q).chosen.biUnion A) ⊆
      (U \ (P.vertices ∪ P.chosen.biUnion A)) ∪
      (P.vertices \ (Q.vertices ∪ Q.chosen.biUnion A)) := by
    intro v hv
    simp only [compose, Finset.union_biUnion, Finset.mem_sdiff, Finset.mem_union] at *
    tauto
  exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

end PackingState

/-- Iteration with stopping when the requested small residual has already
been reached. All choices are finite and use the one-round theorem. -/
lemma nibble_iteration (U : Finset V) (S : Finset E) (A : E → Finset V)
    {r : ℕ} (hr0 : 1 ≤ r) (k : ℕ) {D ε C a K d : ℝ}
    (hD : 0 < D) (he : 0 ≤ ε) (hC : 0 ≤ C)
    (ha : 0 < a) (ha16 : a ≤ 1/16) (hra : (r : ℝ)*a ≤ 1/4)
    (hK : 0 ≤ K) (_hd : 0 < d)
    (hDmin : 1 ≤ (1-((r-1 : ℕ) : ℝ)*a)^k*D)
    (hecap : (1+2*(r : ℝ)*a)^k*(ε+8*(r : ℝ)^2*a^2*D*k) ≤
      (1-((r-1 : ℕ) : ℝ)*a)^k*D/4)
    (hCmin : C ≤ a*((1-((r-1 : ℕ) : ℝ)*a)^k*D))
    (hcode : U.card*C ≤ K*((1-((r-1 : ℕ) : ℝ)*a)^k*D))
    (hsize : 512*(r : ℝ) ≤ a*d*U.card)
    (hmany : 16*(r : ℝ)^2*(K+1)^2 ≤ a^5*d*U.card)
    (hcontract : (1-a/2)^k ≤ d)
    (hsub : ∀ e ∈ S, A e ⊆ U) (hr : ∀ e ∈ S, (A e).card = r)
    (hdeg : ∀ v ∈ U, |((incident S A v).card : ℝ) - D| ≤ ε)
    (hcodeg : ∀ v ∈ U, ∀ w ∈ U, v ≠ w →
      ((incident S A v ∩ incident S A w).card : ℝ) ≤ C) :
    ∃ P : PackingState U S A,
      ((P.vertices.card : ℝ) ≤ d*U.card) ∧
      (((U \ (P.vertices ∪ P.chosen.biUnion A)).card : ℝ) ≤
        k*(16*(r : ℝ)+1)*a^2*U.card) := by
  classical
  let q : ℝ := 1-((r-1 : ℕ) : ℝ)*a
  let g : ℝ := 1+2*(r : ℝ)*a
  let b : ℝ := 1-a/2
  let er : ℕ → ℝ := fun i ↦ g^i*(ε+8*(r : ℝ)^2*a^2*D*i)
  let c : ℝ := (16*(r : ℝ)+1)*a^2
  have hr0' : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hrle : ((r-1 : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.sub_le r 1
  have hq0 : 0 ≤ q := by
    have hh := mul_le_mul_of_nonneg_right hrle ha.le
    dsimp [q]
    linarith
  have hq1 : q ≤ 1 := by dsimp [q]; linarith [mul_nonneg (Nat.cast_nonneg (r-1)) ha.le]
  have hg : 1 ≤ g := by dsimp [g]; nlinarith only [mul_nonneg hr0' ha.le]
  have hg0 : 0 ≤ g := by linarith
  have hb0 : 0 ≤ b := by dsimp [b]; linarith
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hDibounds (i : ℕ) (hi : i ≤ k) : q^k*D ≤ q^i*D ∧ q^i*D ≤ D := by
    constructor
    · exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hq0 hq1 hi) hD.le
    · exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hq0 hq1) hD.le).trans_eq (one_mul D)
  have hernonneg (i : ℕ) : 0 ≤ er i := by dsimp [er]; positivity
  have herbounds (i : ℕ) (hi : i ≤ k) : er i ≤ q^i*D/4 := by
    have herle : er i ≤ er k := by
      apply mul_le_mul
      · exact pow_le_pow_right₀ hg hi
      · have hh : (i : ℝ) ≤ k := by exact_mod_cast hi
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hh
          (show 0 ≤ 8*(r : ℝ)^2*a^2*D by positivity))
      · positivity
      · positivity
    exact (herle.trans hecap).trans (div_le_div_of_nonneg_right (hDibounds i hi).1 (by norm_num))
  have herrec (i : ℕ) : g*er i+8*(r : ℝ)^2*a^2*(q^i*D) ≤ er (i+1) := by
    have hiD : q^i*D ≤ D :=
      (mul_le_mul_of_nonneg_right (pow_le_one₀ hq0 hq1) hD.le).trans_eq (one_mul D)
    have hgpow : 1 ≤ g^(i+1) := one_le_pow₀ hg
    have hcD : 0 ≤ 8*(r : ℝ)^2*a^2*D := by positivity
    have hh : 8*(r : ℝ)^2*a^2*(q^i*D) ≤ g^(i+1)*(8*(r : ℝ)^2*a^2*D) := by
      calc
        _ ≤ 8*(r : ℝ)^2*a^2*D := mul_le_mul_of_nonneg_left hiD (by positivity)
        _ ≤ _ := by simpa using mul_le_mul_of_nonneg_right hgpow hcD
    have heq : er (i+1) = g*er i + g^(i+1)*(8*(r : ℝ)^2*a^2*D) := by
      dsimp [er]
      rw [pow_succ]
      push_cast
      ring
    rw [heq]
    exact add_le_add le_rfl hh
  have hiter : ∀ i ≤ k, ∃ P : PackingState U S A,
      (((P.vertices.card : ℝ) ≤ d*U.card) ∨
        ((P.vertices.card : ℝ) ≤ b^i*U.card) ∧
        ∀ v ∈ P.vertices, |((incident P.edges A v).card : ℝ)-q^i*D| ≤ er i) ∧
      (((U \ (P.vertices ∪ P.chosen.biUnion A)).card : ℝ) ≤ i*c*U.card) := by
    intro i
    induction i with
    | zero =>
      intro hi
      refine ⟨PackingState.initial U S A hsub, Or.inr ⟨?_, ?_⟩, ?_⟩
      · simp [PackingState.initial]
      · simpa [PackingState.initial, er] using hdeg
      · simp [PackingState.initial]
    | succ i ih =>
      intro hik
      have hik' : i ≤ k := (Nat.le_succ i).trans hik
      obtain ⟨P, hP, hwasteP⟩ := ih hik'
      rcases hP with hsmall | ⟨hcount, hregular⟩
      · refine ⟨P, Or.inl hsmall, hwasteP.trans ?_⟩
        have hh : (i : ℝ) ≤ (i+1 : ℕ) := by exact_mod_cast Nat.le_succ i
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh hc0) (Nat.cast_nonneg U.card)
      · by_cases hsmall : (P.vertices.card : ℝ) ≤ d*U.card
        · refine ⟨P, Or.inl hsmall, hwasteP.trans ?_⟩
          have hh : (i : ℝ) ≤ (i+1 : ℕ) := by exact_mod_cast Nat.le_succ i
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh hc0) (Nat.cast_nonneg U.card)
        have hlarge : d*U.card < (P.vertices.card : ℝ) := lt_of_not_ge hsmall
        have hni : (P.vertices.card : ℝ) ≤ U.card := Nat.cast_le.mpr (Finset.card_le_card P.vertices_sub)
        have hDi : 1 ≤ q^i*D := hDmin.trans (hDibounds i hik').1
        have hcodei : P.vertices.card*C ≤ K*(q^i*D) :=
          (mul_le_mul_of_nonneg_right hni hC).trans
            (hcode.trans (mul_le_mul_of_nonneg_left (hDibounds i hik').1 hK))
        have hsizei : 512*(r : ℝ) ≤ a*P.vertices.card := by
          have hh := mul_le_mul_of_nonneg_left hlarge.le ha.le
          nlinarith only [hsize, hh]
        have hmanyi : 16*(r : ℝ)^2*(K+1)^2 ≤ a^5*P.vertices.card := by
          have hh := mul_le_mul_of_nonneg_left hlarge.le (show 0 ≤ a^5 by positivity)
          nlinarith only [hmany, hh]
        have hcodegi : ∀ v ∈ P.vertices, ∀ w ∈ P.vertices, v ≠ w →
            ((incident P.edges A v ∩ incident P.edges A w).card : ℝ) ≤ C := by
          intro v hv w hw hvw
          apply (Nat.cast_le.mpr (Finset.card_le_card (Finset.inter_subset_inter
            (incident_mono P.edges_sub A v) (incident_mono P.edges_sub A w)))).trans
          exact hcodeg v (P.vertices_sub hv) w (P.vertices_sub hw) hvw
        obtain ⟨W, T, M, hWU, hTS, hTW, hMS, hmatch, hsep, hWcard, hwaste, hreg⟩ :=
          one_round P.vertices P.edges A hr0 hDi (hernonneg i) (herbounds i hik') hC
            ha ha16 hra hK hcodei
            (hCmin.trans (mul_le_mul_of_nonneg_left (hDibounds i hik').1 ha.le))
            hsizei hmanyi P.support (fun e he ↦ hr e (P.edges_sub he)) hregular hcodegi
        let Q : PackingState P.vertices P.edges A := ⟨W,T,M,hWU,hTS,hTW,hMS,hmatch,hsep⟩
        refine ⟨P.compose Q, Or.inr ⟨?_, ?_⟩, ?_⟩
        · change (W.card : ℝ) ≤ b^(i+1)*U.card
          calc
            _ ≤ b*P.vertices.card := hWcard
            _ ≤ b*(b^i*U.card) := mul_le_mul_of_nonneg_left hcount hb0
            _ = _ := by rw [pow_succ]; ring
        · intro v hv
          change |((incident T A v).card : ℝ)-q^(i+1)*D| ≤ er (i+1)
          have hh := hreg v hv
          have heq : (1-((r-1 : ℕ) : ℝ)*a)*(q^i*D) = q^(i+1)*D := by
            change q*(q^i*D) = _
            rw [pow_succ]
            ring
          rw [heq] at hh
          exact hh.trans (herrec i)
        · apply (PackingState.compose_waste P Q).trans
          change (U \ (P.vertices ∪ P.chosen.biUnion A)).card +
            ((P.vertices \ (W ∪ M.biUnion A)).card : ℝ) ≤ (i+1 : ℕ)*c*U.card
          have hh := mul_le_mul_of_nonneg_left hni hc0
          change ((P.vertices \ (W ∪ M.biUnion A)).card : ℝ) ≤ c*P.vertices.card at hwaste
          push_cast
          nlinarith only [hwasteP, hwaste, hh]
  obtain ⟨P, hP, hwaste⟩ := hiter k le_rfl
  refine ⟨P, ?_, ?_⟩
  · rcases hP with hsmall | ⟨hbound, _⟩
    · exact hsmall
    · exact hbound.trans (mul_le_mul_of_nonneg_right hcontract (Nat.cast_nonneg U.card))
  · simpa only [c, mul_assoc] using hwaste

open Filter Topology

end Hypergraph

end Nibble
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Nibble
open scoped BigOperators
open Finset


theorem solution.{uE,uV} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Nibble.nibble_iteration.{uE,uV} := @_root_.OAI.AsymptoticallyMinimalLittlewood.Nibble.nibble_iteration.{uE,uV}

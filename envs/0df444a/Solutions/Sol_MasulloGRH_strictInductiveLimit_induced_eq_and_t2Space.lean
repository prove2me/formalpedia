-- Prove2me | solution 1 for MasulloGRH.strictInductiveLimit_induced_eq_and_t2Space
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:22:48.983369+00:00
-- url     : https://prove2.me/submissions/f437fd91-586e-4653-a0f0-77d271163528

import Mathlib
import Definitions.Def_MasulloGRH_LocallyConvex

open Topology

set_option autoImplicit false

namespace Sol_MasulloGRH_strictInductiveLimit_induced_eq_and_t2Space

open MasulloGRH

/-- The infimal convolution of a seminorm `p` on `M` and a seminorm `r` on `F` along a linear map
`i : M → F`: the seminorm `x ↦ ⨅ m, p m + r (x - i m)` on `F`. -/
noncomputable def infConv {M F : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup F]
    [Module ℂ F] (i : M →ₗ[ℂ] F) (p : Seminorm ℂ M) (r : Seminorm ℂ F) : Seminorm ℂ F :=
  Seminorm.of (fun x => ⨅ m : M, p m + r (x - i m))
    (by
      intro x y
      refine le_ciInf_add_ciInf fun u v => ?_
      refine ciInf_le_of_le ⟨0, ?_⟩ (u + v) ?_
      · rintro _ ⟨m, rfl⟩
        positivity
      · have h1 : p (u + v) ≤ p u + p v := map_add_le_add p u v
        have h2 : r (x + y - i (u + v)) ≤ r (x - i u) + r (y - i v) := by
          have h3 : x + y - i (u + v) = (x - i u) + (y - i v) := by
            rw [map_add]; abel
          rw [h3]
          exact map_add_le_add r _ _
        linarith)
    (by
      intro a x
      obtain rfl | ha := eq_or_ne a 0
      · rw [norm_zero, zero_mul, zero_smul]
        refine ciInf_eq_of_forall_ge_of_forall_gt_exists_lt (fun m => by positivity)
          fun w hw => ⟨0, ?_⟩
        simpa using hw
      · rw [Real.mul_iInf_of_nonneg (norm_nonneg a)]
        refine Function.Surjective.iInf_congr (fun m : M => a⁻¹ • m)
          (fun u => ⟨a • u, inv_smul_smul₀ ha u⟩) fun u => ?_
        have h1 : p u = ‖a‖ * p (a⁻¹ • u) := by
          rw [← map_smul_eq_mul p, smul_inv_smul₀ ha]
        have h2 : r (a • x - i u) = ‖a‖ * r (x - i (a⁻¹ • u)) := by
          rw [← map_smul_eq_mul r, smul_sub, map_smul, smul_inv_smul₀ ha]
        rw [h1, h2, mul_add])

theorem infConv_apply {M F : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup F]
    [Module ℂ F] (i : M →ₗ[ℂ] F) (p : Seminorm ℂ M) (r : Seminorm ℂ F) (x : F) :
    infConv i p r x = ⨅ m : M, p m + r (x - i m) := rfl

theorem infConv_bddBelow {M F : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup F]
    [Module ℂ F] (i : M →ₗ[ℂ] F) (p : Seminorm ℂ M) (r : Seminorm ℂ F) (x : F) :
    BddBelow (Set.range fun m : M => p m + r (x - i m)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨m, rfl⟩
  positivity

/-- **Extension of a continuous seminorm from a subspace.**  If `M` carries the topology induced
from a locally convex space `F` by a linear map `i`, every continuous seminorm on `M` is the
restriction along `i` of a continuous seminorm on `F`. -/
theorem exists_seminorm_extension {M F : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup F]
    [Module ℂ F] [tM : TopologicalSpace M] [tF : TopologicalSpace F]
    (hF : IsLocallyConvexTopology F tF) (i : M →ₗ[ℂ] F)
    (hi : tM = TopologicalSpace.induced i tF) (p : Seminorm ℂ M) (hp : Continuous p) :
    ∃ r : Seminorm ℂ F, Continuous r ∧ ∀ m, r (i m) = p m := by
  obtain ⟨ι, _, q, hq⟩ := hF
  have hind : IsInducing i := ⟨hi⟩
  obtain ⟨s, C, -, hle⟩ := Seminorm.bound_comp_of_isInducing hp hq hind
  have hgrp : IsTopologicalAddGroup F := hq.topologicalAddGroup
  have hR : Continuous (C • s.sup q) :=
    Continuous.const_smul (Seminorm.continuous_finsetSup fun k _ => hq.continuous_seminorm k) C
  refine ⟨infConv i p (C • s.sup q), ?_, ?_⟩
  · refine Seminorm.continuous_of_le hR ?_
    intro x
    rw [infConv_apply]
    refine ciInf_le_of_le (infConv_bddBelow i p _ x) 0 ?_
    simp
  · intro m
    rw [infConv_apply]
    apply le_antisymm
    · refine ciInf_le_of_le (infConv_bddBelow i p _ (i m)) m ?_
      simp
    · refine le_ciInf fun m' => ?_
      have h1 : p m ≤ p m' + p (m - m') := by
        have := map_add_le_add p m' (m - m')
        rwa [add_sub_cancel] at this
      have h2 : p (m - m') ≤ (C • s.sup q) (i m - i m') := by
        have h3 : p (m - m') ≤ ((C • s.sup q).comp i) (m - m') := Seminorm.le_def.1 hle (m - m')
        rwa [Seminorm.comp_apply, map_sub i] at h3
      linarith

section chain

variable {E : Type*} [AddCommGroup E] [Module ℂ E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
  (τ : ∀ n, TopologicalSpace (X n))

include hmono in
/-- In a strict sequence all inclusions `X a → X b`, `a ≤ b`, are continuous. -/
theorem continuous_inclusion
    (hstrict : ∀ n, τ n =
      TopologicalSpace.induced (Submodule.inclusion (hmono (Nat.le_succ n))) (τ (n + 1)))
    {a b : ℕ} (h : a ≤ b) :
    @Continuous (X a) (X b) (τ a) (τ b) (Submodule.inclusion (hmono h)) := by
  induction b, h using Nat.le_induction with
  | base => exact @continuous_id _ (τ a)
  | succ b hab ih =>
    have h1 : @Continuous (X b) (X (b + 1)) (τ b) (τ (b + 1))
        (Submodule.inclusion (hmono (Nat.le_succ b))) :=
      continuous_iff_le_induced.2 (hstrict b).le
    exact @Continuous.comp (X a) (X b) (X (b + 1)) (τ a) (τ b) (τ (b + 1)) _ _ h1 ih

/-- **Key step.**  In a strict sequence, a continuous seminorm on a step `X n` extends to a
seminorm on the union `E` whose restriction to every step is continuous. -/
theorem exists_seminorm_of_stage (hexh : ∀ x : E, ∃ n, x ∈ X n)
    (hlc : ∀ n, IsLocallyConvexTopology (X n) (τ n))
    (hstrict : ∀ n, τ n =
      TopologicalSpace.induced (Submodule.inclusion (hmono (Nat.le_succ n))) (τ (n + 1)))
    (n : ℕ) (p : Seminorm ℂ (X n)) (hp : @Continuous (X n) ℝ (τ n) _ p) :
    ∃ Q : Seminorm ℂ E,
      (∀ m, @Continuous (X m) ℝ (τ m) _ (fun x : X m => Q (x : E))) ∧
        ∀ x : X n, Q (x : E) = p x := by
  -- one step of the extension: from `X a` to `X (a + 1)`
  have hstep : ∀ (a : ℕ) (Q : Seminorm ℂ E), ∃ Q' : Seminorm ℂ E,
      @Continuous (X a) ℝ (τ a) _ (fun x : X a => Q (x : E)) →
        @Continuous (X (a + 1)) ℝ (τ (a + 1)) _ (fun x : X (a + 1) => Q' (x : E)) ∧
          ∀ x ∈ X a, Q' x = Q x := by
    intro a Q
    by_cases hQ : @Continuous (X a) ℝ (τ a) _ (fun x : X a => Q (x : E))
    · obtain ⟨r, hr, hrp⟩ := @exists_seminorm_extension (X a) (X (a + 1)) _ _ _ _ (τ a)
        (τ (a + 1)) (hlc (a + 1)) (Submodule.inclusion (hmono (Nat.le_succ a))) (hstrict a)
        (Q.comp (X a).subtype) hQ
      obtain ⟨π, hπ⟩ :=
        (X (a + 1)).subtype.exists_leftInverse_of_injective (X (a + 1)).ker_subtype
      have hπ' : ∀ y : X (a + 1), π (y : E) = y := fun y => LinearMap.congr_fun hπ y
      refine ⟨r.comp π, fun _ => ⟨?_, ?_⟩⟩
      · have h1 : (fun x : X (a + 1) => (r.comp π) (x : E)) = r := by
          funext x
          rw [Seminorm.comp_apply, hπ']
        rw [h1]
        exact hr
      · intro x hx
        have h1 : π x = Submodule.inclusion (hmono (Nat.le_succ a)) ⟨x, hx⟩ :=
          hπ' (Submodule.inclusion (hmono (Nat.le_succ a)) ⟨x, hx⟩)
        rw [Seminorm.comp_apply, h1, hrp ⟨x, hx⟩]
        rfl
    · exact ⟨Q, fun h => absurd h hQ⟩
  choose step hstep using hstep
  -- start: transport `p` to `E` along a linear retraction of `X n`
  obtain ⟨π₀, hπ₀⟩ := (X n).subtype.exists_leftInverse_of_injective (X n).ker_subtype
  have hπ₀' : ∀ y : X n, π₀ (y : E) = y := fun y => LinearMap.congr_fun hπ₀ y
  let seq : ℕ → Seminorm ℂ E := fun k => Nat.rec (p.comp π₀) (fun k Q => step (n + k) Q) k
  have hcont : ∀ k, @Continuous (X (n + k)) ℝ (τ (n + k)) _
      (fun x : X (n + k) => seq k (x : E)) := by
    intro k
    induction k with
    | zero =>
      have h1 : (fun x : X n => seq 0 (x : E)) = p := by
        funext x
        show p (π₀ (x : E)) = p x
        rw [hπ₀']
      show @Continuous (X n) ℝ (τ n) _ (fun x : X n => seq 0 (x : E))
      rw [h1]
      exact hp
    | succ k ih => exact (hstep (n + k) (seq k) ih).1
  have hagree : ∀ k, ∀ x ∈ X (n + k), seq (k + 1) x = seq k x := fun k x hx =>
    (hstep (n + k) (seq k) (hcont k)).2 x hx
  have hagree' : ∀ k l, k ≤ l → ∀ x ∈ X (n + k), seq l x = seq k x := by
    intro k l hkl
    induction l, hkl using Nat.le_induction with
    | base => intro x _; rfl
    | succ l hkl ih =>
      intro x hx
      exact (hagree l x (hmono (Nat.add_le_add_left hkl n) hx)).trans (ih x hx)
  have hex : ∀ x : E, ∃ k, x ∈ X (n + k) := fun x => by
    obtain ⟨m, hm⟩ := hexh x
    exact ⟨m, hmono (Nat.le_add_left m n) hm⟩
  choose K hK using hex
  have hval : ∀ x k, x ∈ X (n + k) → seq (K x) x = seq k x := by
    intro x k hk
    rcases le_total (K x) k with h | h
    · exact (hagree' _ _ h x (hK x)).symm
    · exact hagree' _ _ h x hk
  -- the limit seminorm
  let Q : Seminorm ℂ E := Seminorm.of (fun x => seq (K x) x)
    (by
      intro x y
      have hx : x ∈ X (n + max (K x) (K y)) :=
        hmono (Nat.add_le_add_left (le_max_left _ _) n) (hK x)
      have hy : y ∈ X (n + max (K x) (K y)) :=
        hmono (Nat.add_le_add_left (le_max_right _ _) n) (hK y)
      show seq (K (x + y)) (x + y) ≤ seq (K x) x + seq (K y) y
      rw [hval (x + y) _ ((X _).add_mem hx hy), hval x _ hx, hval y _ hy]
      exact map_add_le_add _ _ _)
    (by
      intro a x
      show seq (K (a • x)) (a • x) = ‖a‖ * seq (K x) x
      rw [hval (a • x) (K x) ((X _).smul_mem a (hK x))]
      exact map_smul_eq_mul _ _ _)
  have hQ : ∀ x k, x ∈ X (n + k) → Q x = seq k x := fun x k hk => hval x k hk
  refine ⟨Q, ?_, ?_⟩
  · intro m
    have h1 : @Continuous (X (n + m)) ℝ (τ (n + m)) _ (fun x : X (n + m) => Q (x : E)) := by
      have h3 : (fun x : X (n + m) => Q (x : E)) = fun x : X (n + m) => seq m (x : E) :=
        funext fun x => hQ x m x.2
      rw [h3]
      exact hcont m
    have h2 := continuous_inclusion X hmono τ hstrict (Nat.le_add_left m n)
    exact @Continuous.comp (X m) (X (n + m)) ℝ (τ m) (τ (n + m)) _ _ _ h1 h2
  · intro x
    have h1 : Q (x : E) = seq 0 (x : E) := hQ x 0 x.2
    rw [h1]
    show p (π₀ (x : E)) = p x
    rw [hπ₀']

end chain

end Sol_MasulloGRH_strictInductiveLimit_induced_eq_and_t2Space

open MasulloGRH Sol_MasulloGRH_strictInductiveLimit_induced_eq_and_t2Space

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    (X : ℕ → Submodule ℂ E) (hmono : Monotone X) (hexh : ∀ x : E, ∃ n, x ∈ X n)
    (τ : ∀ n, TopologicalSpace (X n)) (hlc : ∀ n, IsLocallyConvexTopology (X n) (τ n))
    (hstrict : ∀ n, τ n =
      TopologicalSpace.induced (Submodule.inclusion (hmono (Nat.le_succ n))) (τ (n + 1))) :
    let t : TopologicalSpace E :=
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E (τ n) t Subtype.val}
    (∀ n, TopologicalSpace.induced (Subtype.val : X n → E) t = τ n) ∧
      ((∀ n, @T2Space (X n) (τ n)) → @T2Space E t) := by
  intro t
  -- the family `P` of all seminorms on `E` that are continuous on every step
  let κ : Type _ :=
    {p : Seminorm ℂ E // ∀ n, @Continuous (X n) ℝ (τ n) _ (fun x : X n => p (x : E))}
  have hκ : Nonempty κ := ⟨⟨0, fun n => by simpa using @continuous_const _ _ (τ n) _ _⟩⟩
  let P : SeminormFamily ℂ E κ := fun i => i.1
  -- the topology `t₀` defined by the family `P`
  let t₀ : TopologicalSpace E := P.moduleFilterBasis.topology
  have hP : @WithSeminorms ℂ E κ _ _ _ P t₀ := @WithSeminorms.mk ℂ E κ _ _ _ P t₀ rfl
  have hgrp₀ : @IsTopologicalAddGroup E t₀ _ := by
    let _ : TopologicalSpace E := t₀
    exact hP.topologicalAddGroup
  have hgrpτ : ∀ n, @IsTopologicalAddGroup (X n) (τ n) _ := by
    intro n
    obtain ⟨ι, _, q, hq⟩ := hlc n
    let _ : TopologicalSpace (X n) := τ n
    exact hq.topologicalAddGroup
  -- every inclusion is continuous for `t₀`
  have hf₀ : ∀ n, @Continuous (X n) E (τ n) t₀ Subtype.val := by
    intro n
    let _ : TopologicalSpace E := t₀
    let _ : TopologicalSpace (X n) := τ n
    have := hgrpτ n
    refine WithSeminorms.continuous_of_continuous_comp (q := P) hP (X n).subtype ?_
    intro i
    exact i.2 n
  have hmem : t₀ ∈ {t | IsLocallyConvexTopology E t ∧
      ∀ n, @Continuous (X n) E (τ n) t Subtype.val} := ⟨⟨κ, hκ, P, hP⟩, hf₀⟩
  have hle : t ≤ t₀ := sInf_le hmem
  -- `t₀` is finer than every locally convex topology making the inclusions continuous
  have hge : t₀ ≤ t := by
    refine le_sInf ?_
    rintro s ⟨⟨κ', _, q, hq⟩, hs⟩
    have hqk : ∀ k, @Continuous E ℝ s _ (q k) := by
      intro k
      let _ : TopologicalSpace E := s
      exact hq.continuous_seminorm k
    have hstage : ∀ k n, @Continuous (X n) ℝ (τ n) _ (fun x : X n => q k (x : E)) := fun k n =>
      @Continuous.comp (X n) E ℝ (τ n) s _ (fun x => (x : E)) (fun y => q k y) (hqk k) (hs n)
    have hcont : ∀ k, @Continuous E ℝ t₀ _ (q k) := by
      intro k
      let _ : TopologicalSpace E := t₀
      exact hP.continuous_seminorm ⟨q k, hstage k⟩
    have hid : @Continuous E E t₀ s (LinearMap.id : E →ₗ[ℂ] E) := by
      refine @WithSeminorms.continuous_of_continuous_comp ℂ ℂ E E κ' _ _ _ _ _ _ (RingHom.id ℂ) _
        q t₀ hgrp₀ s hq LinearMap.id ?_
      intro k
      simpa [Seminorm.comp_id] using hcont k
    exact continuous_id_iff_le.1 hid
  have heq : t = t₀ := le_antisymm hle hge
  -- a seminorm continuous on every step is `t`-continuous
  have hcontP : ∀ Q : Seminorm ℂ E,
      (∀ n, @Continuous (X n) ℝ (τ n) _ (fun x : X n => Q (x : E))) → @Continuous E ℝ t _ Q := by
    intro Q hQ
    rw [heq]
    let _ : TopologicalSpace E := t₀
    exact hP.continuous_seminorm ⟨Q, hQ⟩
  refine ⟨?_, ?_⟩
  · intro n
    apply le_antisymm
    · -- the induced topology is finer than `τ n`: every defining seminorm of `τ n` extends
      obtain ⟨ι, _, q, hq⟩ := hlc n
      have hQi : ∀ i, @Continuous (X n) ℝ (TopologicalSpace.induced Subtype.val t) _ (q i) := by
        intro i
        have hqi : @Continuous (X n) ℝ (τ n) _ (q i) := by
          let _ : TopologicalSpace (X n) := τ n
          exact hq.continuous_seminorm i
        obtain ⟨Q, hQ, hQp⟩ := exists_seminorm_of_stage X hmono τ hexh hlc hstrict n (q i) hqi
        have h1 : (q i : X n → ℝ) = (fun y : E => Q y) ∘ (Subtype.val : X n → E) :=
          funext fun x => (hQp x).symm
        rw [h1]
        exact @Continuous.comp (X n) E ℝ (TopologicalSpace.induced Subtype.val t) t _ _ _
          (hcontP Q hQ) (continuous_induced_dom)
      have hgrpt : @IsTopologicalAddGroup E t _ := by
        rw [heq]; exact hgrp₀
      have hgrp : @IsTopologicalAddGroup (X n) (TopologicalSpace.induced Subtype.val t) _ := by
        let _ : TopologicalSpace E := t
        exact topologicalAddGroup_induced (X n).subtype
      have hid : @Continuous (X n) (X n) (TopologicalSpace.induced Subtype.val t) (τ n)
          (LinearMap.id : X n →ₗ[ℂ] X n) := by
        refine @WithSeminorms.continuous_of_continuous_comp ℂ ℂ (X n) (X n) ι _ _ _ _ _ _
          (RingHom.id ℂ) _ q (TopologicalSpace.induced Subtype.val t) hgrp (τ n) hq
          LinearMap.id ?_
        intro i
        simpa [Seminorm.comp_id] using hQi i
      exact continuous_id_iff_le.1 hid
    · -- the inclusion is continuous
      have h1 : @Continuous (X n) E (τ n) t Subtype.val := by
        rw [heq]; exact hf₀ n
      exact continuous_iff_le_induced.1 h1
  · intro hT2
    rw [heq]
    let _ : TopologicalSpace E := t₀
    have hT1 : T1Space E := by
      refine WithSeminorms.T1_of_separating hP ?_
      intro x hx
      obtain ⟨n, hn⟩ := hexh x
      obtain ⟨ι, _, q, hq⟩ := hlc n
      have hx' : (⟨x, hn⟩ : X n) ≠ 0 := by
        intro h
        exact hx (congrArg Subtype.val h)
      let _ : TopologicalSpace (X n) := τ n
      have hT2n : T2Space (X n) := hT2 n
      obtain ⟨i, hi⟩ := WithSeminorms.separating_of_T1 hq ⟨x, hn⟩ hx'
      obtain ⟨Q, hQ, hQp⟩ := exists_seminorm_of_stage X hmono τ hexh hlc hstrict n (q i)
        (hq.continuous_seminorm i)
      refine ⟨⟨Q, hQ⟩, ?_⟩
      show Q x ≠ 0
      rw [show Q x = q i ⟨x, hn⟩ from hQp ⟨x, hn⟩]
      exact hi
    exact inferInstance

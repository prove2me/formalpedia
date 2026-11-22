-- Prove2me | solution 1 for MasulloGRH.expDecayStage_weighted_domination
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T19:48:04.500548+00:00
-- url     : https://prove2.me/submissions/33c95854-4b34-41ff-9db8-fc39c14c1b4f

import Theorems.Thm_MasulloGRH_schwartzBruhat_modulus_multiplier
import Theorems.Thm_MasulloGRH_expDecayStage_weighted_mem
import Theorems.Thm_MasulloGRH_isCompact_of_isGoodSubgroup
import Theorems.Thm_MasulloGRH_isCompact_moduleKernel_and_compact_le
import Definitions.Def_MasulloGRH_ExpDecayStages
import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

universe u

namespace MasulloGRHWMemAux

open MasulloGRH

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- the kernel of a module as a subgroup -/
def modKer {m : G → ℝ} (hm : IsModule m) : Subgroup G where
  carrier := {g | m g = 1}
  one_mem' := by
    show m 1 = 1
    have h := hm.map_mul 1 1
    rw [mul_one] at h
    have hp := hm.pos 1
    nlinarith
  mul_mem' {a b} ha hb := by
    show m (a * b) = 1
    rw [hm.map_mul, show m a = 1 from ha, show m b = 1 from hb, one_mul]
  inv_mem' {a} ha := by
    show m a⁻¹ = 1
    have h := hm.map_mul a a⁻¹
    rw [mul_inv_cancel, show m a = 1 from ha, one_mul] at h
    have h1 := hm.map_mul 1 1
    rw [mul_one] at h1
    have hp := hm.pos 1
    have : m 1 = 1 := by nlinarith
    rw [← h, this]


lemma ws_all {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] {ι : Type*} {p : SeminormFamily ℂ E ι} (hp : WithSeminorms p) :
    WithSeminorms (fun q : {q : Seminorm ℂ E // Continuous q} => q.1) := by
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf]
  refine le_antisymm (le_iInf fun q => ?_) ?_
  · rw [← Filter.tendsto_iff_comap]
    have := q.2.tendsto 0
    rwa [map_zero] at this
  · rw [(SeminormFamily.withSeminorms_iff_nhds_eq_iInf p).1 hp]
    exact le_iInf fun i => iInf_le_of_le ⟨p i, hp.continuous_seminorm i⟩ le_rfl

/-- a `WithSeminorms` topology, with any index, is locally convex -/
lemma lc_of_ws {E : Type u} [AddCommGroup E] [Module ℂ E] (t : TopologicalSpace E)
    {ι : Type*} {p : SeminormFamily ℂ E ι} (hp : @WithSeminorms ℂ E ι _ _ _ p t) :
    IsLocallyConvexTopology E t := by
  letI := t
  haveI : IsTopologicalAddGroup E := hp.topologicalAddGroup
  exact ⟨{q : Seminorm ℂ E // Continuous q}, ⟨⟨0, continuous_const⟩⟩, _, ws_all hp⟩

/-- an infimum of locally convex topologies is locally convex -/
lemma lc_sInf {E : Type u} [AddCommGroup E] [Module ℂ E] (S : Set (TopologicalSpace E))
    (hS : ∀ t ∈ S, IsLocallyConvexTopology E t) : IsLocallyConvexTopology E (sInf S) := by
  choose ι _ p hp using fun t : S => hS t.1 t.2
  rw [sInf_eq_iInf']
  exact lc_of_ws _ (withSeminorms_iInf (p := p) (t := fun t : S => t.1) hp)

variable {H : Type u} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- the topology of `S(H)` is locally convex -/
lemma sb_lc : IsLocallyConvexTopology (SchwartzBruhat H) inferInstance :=
  lc_sInf _ fun _ ht => ht.1


end MasulloGRHWMemAux

open MasulloGRH MasulloGRHWMemAux in
theorem solution
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (m : G → ℝ) (hm : IsRposModule m)
    (I : Set ℝ) (hI : I.OrdConnected) (hne : I.Nonempty) (k : Subgroup G) (hk : IsGoodSubgroup k)
    (a₁ a a₂ : ℝ) (h₁ : a₁ ∈ I) (h₂ : a₂ ∈ I) (hle₁ : a₁ ≤ a) (hle₂ : a ≤ a₂) :
    @Continuous (ExpDecayStage G m I k) (SchwartzBruhat (G ⧸ k))
      (TopologicalSpace.induced (fun y : ExpDecayStage G m I k =>
          ExpDecaySchwartz.weighted k a₁ y.1) inferInstance ⊓
        TopologicalSpace.induced (fun y : ExpDecayStage G m I k =>
          ExpDecaySchwartz.weighted k a₂ y.1) inferInstance) _
      (fun y : ExpDecayStage G m I k => ExpDecaySchwartz.weighted k a y.1) := by
  classical
  have ha : a ∈ I := hI.out h₁ h₂ ⟨hle₁, hle₂⟩
  haveI : IsClosed (k : Set G) := hk.1
  have hm1 : ∀ h ∈ k, m h = 1 := by
    intro h hh
    exact (isCompact_moduleKernel_and_compact_le G m hm (modKer hm.1) (fun g => Iff.rfl)).2
      k (isCompact_of_isGoodSubgroup G k hk) hh
  -- the modulus on `G ⧸ k`
  let μ : G ⧸ k → ℝ := fun x => m x.out
  have hμmk : ∀ g : G, μ (QuotientGroup.mk g) = m g := by
    intro g
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul k g
    show m (QuotientGroup.mk g : G ⧸ k).out = m g
    rw [hh, hm.1.map_mul, hm1 h h.2, mul_one]
  have hμc : Continuous μ := by
    refine continuous_coinduced_dom.2 ?_
    convert hm.1.continuous using 1
    exact funext hμmk
  have hμp : ∀ x, 0 < μ x := fun x => hm.1.pos _
  have hμm : ∀ x y, μ (x * y) = μ x * μ y := by
    intro x y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, hμmk, hμmk, hμmk, hm.1.map_mul]
  obtain ⟨M, hM⟩ := schwartzBruhat_modulus_multiplier (G ⧸ k) μ hμc hμp hμm (a₁ - a) (a₂ - a)
    (by linarith) (by linarith)
  -- unfold the weighted operators
  have hW : ∀ (b : ℝ) (hb : b ∈ I) (y : ExpDecayStage G m I k),
      (ExpDecaySchwartz.weighted k b y.1).1 = fun x : G ⧸ k => ((m x.out ^ b : ℝ) : ℂ) * y.1.toFun x.out := by
    intro b hb y
    have hmem := expDecayStage_weighted_mem G m hm I hI hne k hk y b hb
    unfold ExpDecaySchwartz.weighted
    first | (erw [dif_pos hmem]) | (rw [dif_pos hmem]) | simp only [dif_pos hmem]
  have hEq : (fun y : ExpDecayStage G m I k => ExpDecaySchwartz.weighted k a y.1) =
      fun y => M (ExpDecaySchwartz.weighted k a₁ y.1 + ExpDecaySchwartz.weighted k a₂ y.1) := by
    funext y
    apply Subtype.ext
    funext x
    have h := hM (ExpDecaySchwartz.weighted k a₁ y.1 + ExpDecaySchwartz.weighted k a₂ y.1) x
    show (ExpDecaySchwartz.weighted k a y.1).1 x = (M _).toFun x
    rw [h, hW a ha]
    show _ = _ * ((ExpDecaySchwartz.weighted k a₁ y.1).1 x + (ExpDecaySchwartz.weighted k a₂ y.1).1 x)
    rw [hW a₁ h₁, hW a₂ h₂]
    have ht : 0 < m x.out := hm.1.pos _
    show ((m x.out ^ a : ℝ) : ℂ) * y.1.toFun x.out =
      ((m x.out ^ (a₁ - a) + m x.out ^ (a₂ - a) : ℝ)⁻¹ : ℂ) *
        (((m x.out ^ a₁ : ℝ) : ℂ) * y.1.toFun x.out + ((m x.out ^ a₂ : ℝ) : ℂ) * y.1.toFun x.out)
    have e1 : m x.out ^ a₁ = m x.out ^ (a₁ - a) * m x.out ^ a := by
      rw [← Real.rpow_add ht]; ring_nf
    have e2 : m x.out ^ a₂ = m x.out ^ (a₂ - a) * m x.out ^ a := by
      rw [← Real.rpow_add ht]; ring_nf
    have hS : (m x.out ^ (a₁ - a) + m x.out ^ (a₂ - a) : ℝ) ≠ 0 := by
      have := Real.rpow_pos_of_pos ht (a₁ - a)
      have := Real.rpow_pos_of_pos ht (a₂ - a)
      linarith
    have hS' : ((m x.out ^ (a₁ - a) + m x.out ^ (a₂ - a) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hS
    rw [e1, e2]
    push_cast at hS' ⊢
    field_simp
  rw [hEq]
  obtain ⟨ι, _, p, hp⟩ := sb_lc (H := G ⧸ k)
  haveI : IsTopologicalAddGroup (SchwartzBruhat (G ⧸ k)) := hp.topologicalAddGroup
  letI t : TopologicalSpace (ExpDecayStage G m I k) :=
    TopologicalSpace.induced (fun y : ExpDecayStage G m I k =>
          ExpDecaySchwartz.weighted k a₁ y.1) inferInstance ⊓
        TopologicalSpace.induced (fun y : ExpDecayStage G m I k =>
          ExpDecaySchwartz.weighted k a₂ y.1) inferInstance
  have c1 : Continuous fun y : ExpDecayStage G m I k => ExpDecaySchwartz.weighted k a₁ y.1 :=
    continuous_iff_le_induced.2 inf_le_left
  have c2 : Continuous fun y : ExpDecayStage G m I k => ExpDecaySchwartz.weighted k a₂ y.1 :=
    continuous_iff_le_induced.2 inf_le_right
  exact M.continuous.comp (c1.add c2)

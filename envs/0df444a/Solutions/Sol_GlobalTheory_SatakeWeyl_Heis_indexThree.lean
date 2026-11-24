-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.Heis.indexThree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:04:15.319337+00:00
-- url     : https://prove2.me/submissions/c9d84a8d-9348-4fec-92b6-1dec8a9212c6

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryRankThreeRootIndexOfCards
import Theorems.Thm_GlobalTheory_SatakeWeyl_Heis_index_eq_map_mul_ker
import Theorems.Thm_GlobalTheory_SatakeWeyl_Heis_exists_heis
import Theorems.Thm_GlobalTheory_SatakeWeyl_Heis_mem_int_iff
import Theorems.Thm_GlobalTheory_SatakeWeyl_Heis_conj_iff
import Theorems.Thm_GlobalTheory_SatakeWeyl_Heis_heis_mul
import Theorems.Thm_GlobalTheory_SatakeWeyl_Heis_heis_01
import Theorems.Thm_GlobalTheory_SatakeWeyl_Heis_heis_02
import Theorems.Thm_GlobalTheory_SatakeWeyl_Heis_exists_snd
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_SatakeWeyl_mat_injective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.Heis
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}
namespace GlobalTheory.SatakeWeyl.Heis
theorem _root_.solution : IntIndex → TraceZeroIndex → IndexThree := by
  intro hI hT L _ _ ϖ σ q hU s hs
  have hI := hI L ϖ σ q hU
  have hT := hT L ϖ σ q hU
  have hsnd := fun x => exists_snd hU (x := x)
  obtain ⟨hσ, hv, hϖ, hvϖ, -⟩ := hU
  have h0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hvϖ; exact WithZero.zero_ne_coe hvϖ
  have hϖO : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [hvϖ, ← WithZero.coe_one, WithZero.coe_le_coe]
    decide
  set T := (intL L).toAddSubgroup ⊓ (σ.toAddMonoidHom + AddMonoidHom.id L).ker with hTdef
  have mT : ∀ y, y ∈ T ↔ y ∈ intL L ∧ σ y + y = 0 := fun y => Iff.rfl
  set U := KU σ 3 ⊓ rootU σ ![0, 0, 0] with hUdef
  have mU : ∀ g, g ∈ U ↔ ∃ x ∈ intL L, ∃ y ∈ intL L, y + σ y + x * σ x = 0 ∧ mat g = Heisenberg₂ σ x y :=
    mem_int_iff hσ hv
  set V := U.map (MulAut.conj s).toMonoidHom with hVdef
  have mV : ∀ g, g ∈ V ↔ ∃ x ∈ intL L, ∃ y ∈ intL L, y + σ y + x * σ x = 0 ∧
      mat g = Heisenberg₂ σ (ϖ * x) (ϖ * (ϖ * y)) := by
    intro g
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨x, hx, y, hy, hr, e⟩ := (mU u).1 hu
      exact ⟨x, hx, y, hy, hr, conj_iff h0 hϖ hs u x y e⟩
    · rintro ⟨x, hx, y, hy, hr, e⟩
      obtain ⟨u, hu⟩ := exists_heis hσ hr
      exact ⟨u, (mU u).2 ⟨x, hx, y, hy, hr, hu⟩, mat_injective ((conj_iff h0 hϖ hs u x y hu).trans e.symm)⟩
  have VU : V ≤ U := by
    intro g hg
    obtain ⟨x, hx, y, hy, hr, e⟩ := (mV g).1 hg
    refine (mU g).2 ⟨_, mul_mem hϖO hx, _, mul_mem hϖO (mul_mem hϖO hy), ?_, e⟩
    simp only [map_mul, hϖ]
    linear_combination ϖ * ϖ * hr
  let φ : U →* Multiplicative L := MonoidHom.mk' (fun g => Multiplicative.ofAdd (mat g.1 0 1)) (by
    intro a b
    obtain ⟨x, -, y, -, -, e⟩ := (mU a).1 a.2
    obtain ⟨x', -, y', -, -, e'⟩ := (mU b).1 b.2
    rw [← ofAdd_add, Subgroup.coe_mul, mat_mul, e, e', heis_mul]
    rfl)
  have hφ : ∀ g, φ g = Multiplicative.ofAdd (mat g.1 0 1) := fun _ => rfl
  have hker : ∀ g : φ.ker, ∃ y ∈ T, mat g.1.1 = Heisenberg₂ σ 0 y := by
    intro g
    obtain ⟨x, -, y, hy, hr, e⟩ := (mU g.1).1 g.1.2
    have : mat g.1.1 0 1 = 0 := g.2
    rw [e, heis_01] at this
    subst this
    exact ⟨y, (mT y).2 ⟨hy, by linear_combination hr⟩, e⟩
  let χ : φ.ker →* Multiplicative L := MonoidHom.mk' (fun g => Multiplicative.ofAdd (mat g.1.1 0 2)) (by
    intro a b
    obtain ⟨y, -, e⟩ := hker a
    obtain ⟨y', -, e'⟩ := hker b
    rw [← ofAdd_add, Subgroup.coe_mul, Subgroup.coe_mul, mat_mul, e, e', heis_mul, heis_02, heis_02, heis_02,
      zero_mul, sub_zero])
  have r1 : φ.range = AddSubgroup.toSubgroup (intL L).toAddSubgroup := by
    ext z
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨x, hx, y, -, -, e⟩ := (mU g).1 g.2
      show mat g.1 0 1 ∈ intL L
      rw [e]; exact hx
    · intro hz
      obtain ⟨y, hy, hr⟩ := hsnd z.toAdd hz
      obtain ⟨u, hu⟩ := exists_heis hσ hr
      refine ⟨⟨u, (mU u).2 ⟨_, hz, y, hy, hr, hu⟩⟩, ?_⟩
      rw [hφ, hu]; rfl
  have r2 : (V.subgroupOf U).map φ =
      AddSubgroup.toSubgroup ((intL L).toAddSubgroup.map (AddMonoidHom.mulLeft ϖ)) := by
    ext z
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨x, hx, y, -, -, e⟩ := (mV g).1 hg
      refine ⟨x, hx, ?_⟩
      show ϖ * x = mat g.1 0 1
      rw [e]; rfl
    · rintro ⟨x, hx, hz⟩
      have hz : ϖ * x = z.toAdd := hz
      obtain ⟨y, hy, hr⟩ := hsnd x hx
      have hr' : ϖ * (ϖ * y) + σ (ϖ * (ϖ * y)) + ϖ * x * σ (ϖ * x) = 0 := by
        simp only [map_mul, hϖ]
        linear_combination ϖ * ϖ * hr
      obtain ⟨u, hu⟩ := exists_heis hσ hr'
      have huV : u ∈ V := (mV u).2 ⟨x, hx, y, hy, hr, hu⟩
      refine ⟨⟨u, VU huV⟩, huV, ?_⟩
      rw [hφ, hu, heis_01, hz]; rfl
  have r3 : χ.range = AddSubgroup.toSubgroup T := by
    ext z
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨y, hy, e⟩ := hker g
      show mat g.1.1 0 2 ∈ T
      rw [e]; exact hy
    · intro hz
      obtain ⟨hy, hr⟩ := (mT z.toAdd).1 hz
      have hr' : z.toAdd + σ z.toAdd + 0 * σ 0 = 0 := by linear_combination hr
      obtain ⟨u, hu⟩ := exists_heis hσ hr'
      refine ⟨⟨⟨u, (mU u).2 ⟨_, zero_mem _, _, hy, hr', hu⟩⟩, ?_⟩, ?_⟩
      · show mat u 0 1 = 0
        rw [hu]; rfl
      · show Multiplicative.ofAdd (mat u 0 2) = z
        rw [hu]; rfl
  have r4 : (V.subgroupOf U).subgroupOf φ.ker = (AddSubgroup.toSubgroup
      ((T.map (AddMonoidHom.mulLeft ϖ)).map (AddMonoidHom.mulLeft ϖ))).comap χ := by
    ext g
    obtain ⟨w, -, e⟩ := hker g
    constructor
    · intro hg
      obtain ⟨x, hx, y, hy, hr, e'⟩ := (mV g.1.1).1 hg
      have hx0 : ϖ * x = 0 := by rw [← heis_01 (σ := σ) (ϖ * x), ← e', e]; rfl
      have hx0 : x = 0 := (mul_eq_zero.1 hx0).resolve_left h0
      subst hx0
      refine ⟨ϖ * y, ⟨y, (mT y).2 ⟨hy, by linear_combination hr⟩, rfl⟩, ?_⟩
      show ϖ * (ϖ * y) = mat g.1.1 0 2
      rw [e']; rfl
    · rintro ⟨_, ⟨y, hy, rfl⟩, hz⟩
      have hz : ϖ * (ϖ * y) = mat g.1.1 0 2 := hz
      rw [e, heis_02] at hz
      obtain ⟨hy, hr⟩ := (mT y).1 hy
      exact (mV g.1.1).2 ⟨0, zero_mem _, y, hy, by linear_combination hr, by rw [e, mul_zero, hz]⟩
  have TT : T.map (AddMonoidHom.mulLeft ϖ) ≤ T := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hy, hr⟩ := (mT y).1 hy
    refine (mT (ϖ * y)).2 ⟨mul_mem hϖO hy, ?_⟩
    rw [map_mul, hϖ]
    linear_combination ϖ * hr
  have r5 : ((T.map (AddMonoidHom.mulLeft ϖ)).map (AddMonoidHom.mulLeft ϖ)).relIndex T = q * q := by
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ (AddSubgroup.map_mono TT) TT,
      AddSubgroup.relIndex_map_map_of_injective _ _ (mul_right_injective₀ h0), hT]
  have r6 : (V.subgroupOf U).relIndex φ.ker = q * q := by
    rw [Subgroup.relIndex, r4, Subgroup.index_comap, r3, AddSubgroup.relIndex_toSubgroup, r5]
  rw [Subgroup.relIndex, index_eq_map_mul_ker φ, r6, r1, r2, AddSubgroup.relIndex_toSubgroup, hI]
  ring
end GlobalTheory.SatakeWeyl.Heis

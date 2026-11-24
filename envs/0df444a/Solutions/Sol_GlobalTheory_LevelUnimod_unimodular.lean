-- Prove2me | solution 1 for GlobalTheory.LevelUnimod.unimodular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:27:02.308853+00:00
-- url     : https://prove2.me/submissions/723a1e22-06b4-4772-b69e-4ff37ebdf8e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_GlCharacterEqOneOfTransposeInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsUnimodularBlockUpperTriangularSymmetricLevels
import Theorems.Thm_GlobalTheory_LevelUnimod_map_mul_right_eq
import Theorems.Thm_GlobalTheory_LevelUnimod_modular_eq_one
import Theorems.Thm_GlobalTheory_LevelUnimod_modular_restrict
import Theorems.Thm_GlobalTheory_LevelUnimod_levDiag_inv
import Theorems.Thm_GlobalTheory_LevelUnimod_conj_levDiag
import Theorems.Thm_GlobalTheory_LevelUnimod_continuous_flipInv
import Theorems.Thm_GlobalTheory_LevelUnimod_neBot_units
import Theorems.Thm_GlobalTheory_LevelUnimod_infinite_field
import Theorems.Thm_GlobalTheory_LevelUnimod_tendsto_conj
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space
import Theorems.Thm_GlobalTheory_SplitWeil_volGL_haar
import Theorems.Thm_GlobalTheory_StepData_IntM_mul
import Theorems.Thm_GlobalTheory_gl_character_eq_one_of_transpose_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open scoped Topology
open GlobalTheory GlobalTheory.LevelUnimod
namespace GlobalTheory.LevelUnimod
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c l : ℕ) (L : Fin c → ℕ) (_ : ∀ i, L (Fin.rev i) + L i = 2 * l) (S : Subgroup (GL (n ⊕ Fin c) k)) (_ : ∀ g : GL (n ⊕ Fin c) k, g ∈ S ↔ ∀ r s : n ⊕ Fin c, (r.isRight ∨ s.isRight) → Sum.elim (fun _ => l) L s ≤ Sum.elim (fun _ => l) L r → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) (m : Measure S), m.IsHaarMeasure → m.IsMulRightInvariant := by
  intro k _ _ _ _ _ _ n _ _ c l L hL S hS m hm
  haveI := t2Space k
  haveI := infinite_field (k := k)
  haveI := neBot_units (k := k)
  obtain ⟨i1, i2, i3, -⟩ := volGL_haar k (n ⊕ Fin c) Measure.addHaar
  set lev : n ⊕ Fin c → ℕ := Sum.elim (fun _ => l) L with hlev
  have hcl : IsClosed (S : Set (GL (n ⊕ Fin c) k)) := by
    have : (S : Set (GL (n ⊕ Fin c) k)) = ⋂ (r) (s) (_ : r.isRight ∨ s.isRight) (_ : lev s ≤ lev r),
        {g | g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s} := by
      ext g
      simp only [SetLike.mem_coe, hS, Set.mem_iInter, Set.mem_setOf_eq]
    rw [this]
    refine isClosed_iInter fun r => isClosed_iInter fun s => isClosed_iInter fun _ => isClosed_iInter fun _ => ?_
    exact isClosed_eq (Units.continuous_val.matrix_elem r s) continuous_const
  haveI : LocallyCompactSpace S := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology (S : Set (GL (n ⊕ Fin c) k))
  have hX : ∀ x : GL n k, embX c x ∈ S := fun x => by
    rw [hS]
    intro r s hR _
    change fromBlocks x.val 0 0 1 r s = _
    rcases r with r | r <;> rcases s with s | s <;> simp_all [one_apply]

  let σ : n ⊕ Fin c ≃ n ⊕ Fin c := Equiv.sumCongr (Equiv.refl n) Fin.revPerm
  have hσ : ∀ r, σ (σ r) = r := fun r => by rcases r with r | r <;> simp [σ]
  have hσl : ∀ r, lev (σ r) + lev r = 2 * l := fun r => by
    rcases r with r | r
    · simp [σ, hlev, two_mul]
    · simpa [σ, hlev] using hL r
  have hσR : ∀ r, (σ r).isRight = r.isRight := fun r => by rcases r with r | r <;> simp [σ]
  have hflip : ∀ g ∈ S, flipInv σ g ∈ S := fun g hg => by
    rw [hS]
    intro r s hR hle
    change (g⁻¹ : GL (n ⊕ Fin c) k).val (σ s) (σ r) = _
    rw [(hS _).1 (S.inv_mem hg) (σ s) (σ r) (by rw [hσR, hσR]; exact hR.symm)
      (by have := hσl r; have := hσl s; omega)]
    simp only [one_apply, σ.apply_eq_iff_eq, eq_comm]
  have hchar : ∀ x : GL n k, Measure.modularCharacter (⟨embX c x, hX x⟩ : S) = 1 := by
    refine GlobalTheory.gl_character_eq_one_of_transpose_inv k n (Measure.modularCharacter.comp ((embX c).codRestrict S hX)) fun g g' h => ?_
    refine modular_restrict S (flipAut σ hσ) (continuous_flipInv σ) (continuous_flipInv σ) hflip hflip _ _ ?_
    ext r s
    change fromBlocks g'.val 0 0 1 r s = ((embX c g)⁻¹ : GL (n ⊕ Fin c) k).val (σ s) (σ r)
    rw [← map_inv, h]
    change _ = fromBlocks (g⁻¹ : GL n k).val 0 0 1 (σ s) (σ r)
    rcases r with r | r <;> rcases s with s | s <;> simp [σ, one_apply, eq_comm]

  have hconj : ∀ (t : kˣ), ∀ g ∈ S, (levDiag lev t)⁻¹ * g * levDiag lev t ∈ S := fun t g hg => by
    rw [hS]
    intro r s hR hle
    rw [conj_levDiag, (hS _).1 hg r s hR hle]
    by_cases e : r = s
    · subst e
      rw [mul_right_comm, ← mul_pow, Units.inv_mul, one_pow, one_mul]
    · simp only [one_apply_ne e, mul_zero, zero_mul]
  have hone : ∀ g : S, Measure.modularCharacter g = 1 := by
    refine modular_eq_one fun g U hU => ?_
    have t1 := tendsto_conj l L g.1 ((hS _).1 g.2)
    have t2 := tendsto_conj l L (g.1)⁻¹ ((hS _).1 (S.inv_mem g.2))
    rw [← hlev] at t1 t2
    have key : ∀ a b : GL (n ⊕ Fin c) k, a * b = 1 → a ∈ S → b ∈ S →
        a.val.toBlocks₁₁ * b.val.toBlocks₁₁ = 1 := fun a b hab ha hb => by
      have u := (tendsto_conj l L a ((hS _).1 ha)).mul (tendsto_conj l L b ((hS _).1 hb))
      have e : ∀ d : GL (n ⊕ Fin c) k, (d⁻¹ * a * d).val * (d⁻¹ * b * d).val = 1 := fun d => by
        rw [← Units.val_mul, show d⁻¹ * a * d * (d⁻¹ * b * d) = d⁻¹ * (a * b) * d by group, hab]
        simp
      simp only [e] at u
      have := tendsto_nhds_unique u tendsto_const_nhds
      rw [fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at this
      simpa using this.1
    let x : GL n k := ⟨g.1.val.toBlocks₁₁, (g.1)⁻¹.val.toBlocks₁₁,
      key _ _ (mul_inv_cancel _) g.2 (S.inv_mem g.2), key _ _ (inv_mul_cancel _) (S.inv_mem g.2) g.2⟩
    have t3 : Filter.Tendsto (fun t : kˣ => (levDiag lev t)⁻¹ * g.1 * levDiag lev t)
        (Filter.comap (Units.val : kˣ → k) (𝓝 0)) (𝓝 (embX c x)) := by
      rw [Units.isInducing_embedProduct.tendsto_nhds_iff]
      refine Filter.Tendsto.prodMk_nhds t1 ((MulOpposite.continuous_op.tendsto _).comp ?_)
      rw [← map_inv]
      refine t2.congr fun t => ?_
      rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, mul_assoc]
    have t4 : Filter.Tendsto (fun t : kˣ => (⟨(levDiag lev t)⁻¹ * g.1 * levDiag lev t, hconj t _ g.2⟩ : S) *
        (⟨embX c x, hX x⟩ : S)⁻¹) (Filter.comap (Units.val : kˣ → k) (𝓝 0)) (𝓝 1) := by
      rw [← mul_inv_cancel (⟨embX c x, hX x⟩ : S)]
      exact (tendsto_subtype_rng.2 t3).mul tendsto_const_nhds
    obtain ⟨t, ht⟩ := (t4.eventually_mem hU).exists
    refine ⟨_, ht, ?_⟩
    have hi : Measure.modularCharacter (⟨embX c x, hX x⟩ : S)⁻¹ = 1 := by
      rw [← hchar x⁻¹]
      congr 1
    rw [map_mul, hi, mul_one]
    refine modular_restrict S (MulAut.conj (levDiag lev t)⁻¹) ?_ ?_ ?_ ?_ _ _ ?_
    · exact (continuous_const.mul continuous_id).mul continuous_const
    · exact (continuous_const.mul continuous_id).mul continuous_const
    · intro a ha
      simpa using hconj t a ha
    · intro a ha
      have := hconj t⁻¹ a ha
      rw [← levDiag_inv] at this
      simpa using this
    · simp
  exact ⟨fun g => by rw [map_mul_right_eq, hone, one_smul]⟩
end GlobalTheory.LevelUnimod

-- Prove2me | solution 1 for GlobalTheory.torsion_gens_glue_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:37:46.874354+00:00
-- url     : https://prove2.me/submissions/339c01f7-6f33-462d-a993-7287eceb5e89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionTwoGeneratorsGlobal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M]
    [Module (𝓞 F) M] (N : ℕ) (hN : 1 ≤ N) (hfin : Finite {x : M // N • x = 0})
    (H : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → (N : 𝓞 F) ∈ 𝔭 →
      ∃ u v : M, N • u = 0 ∧ N • v = 0 ∧ ∀ x : M, N • x = 0 → ∃ a b : 𝓞 F,
        x - a • u - b • v ∈ 𝔭 • Submodule.torsionBy (𝓞 F) M (N : 𝓞 F)) :
    ∃ p : Fin 2 → M, (∀ i, N • p i = 0) ∧ ∀ y : M, N • y = 0 → ∃ a b : 𝓞 F, y = a • p 0 + b • p 1 := by
  classical
  set T := Submodule.torsionBy (𝓞 F) M (N : 𝓞 F) with hTdef
  have hT : ∀ x, x ∈ T ↔ N • x = 0 := fun x => by
    rw [hTdef, Submodule.mem_torsionBy_iff, Nat.cast_smul_eq_nsmul]
  set J : Ideal (𝓞 F) := Ideal.span {(N : 𝓞 F)} with hJdef
  have hJ : J ≠ ⊥ := by
    rw [hJdef, Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]; omega
  haveI : Finite (𝓞 F ⧸ J) := Ideal.finiteQuotientOfFreeOfNeBot J hJ
  have hPfin : {𝔭 : Ideal (𝓞 F) | 𝔭.IsMaximal ∧ J ≤ 𝔭}.Finite := by
    have key : ∀ 𝔭 𝔮 : Ideal (𝓞 F), J ≤ 𝔮 →
        (Ideal.Quotient.mk J) '' (𝔭 : Set (𝓞 F)) = (Ideal.Quotient.mk J) '' (𝔮 : Set (𝓞 F)) →
        𝔭 ≤ 𝔮 := by
      intro 𝔭 𝔮 hq he x hx
      have hmem : Ideal.Quotient.mk J x ∈ (Ideal.Quotient.mk J) '' (𝔮 : Set (𝓞 F)) :=
        he ▸ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hxy⟩ := hmem
      have hyx : y - x ∈ J := Ideal.Quotient.eq.mp hxy
      have := 𝔮.sub_mem hy (hq hyx)
      simpa using this
    refine Set.Finite.of_finite_image (f := fun 𝔭 : Ideal (𝓞 F) =>
      (Ideal.Quotient.mk J) '' (𝔭 : Set (𝓞 F))) (Set.toFinite _) ?_
    intro 𝔭 h𝔭 𝔮 h𝔮 he
    exact le_antisymm (key _ _ h𝔮.2 he) (key _ _ h𝔭.2 he.symm)
  set P := hPfin.toFinset with hPdef
  have hP : ∀ 𝔭, 𝔭 ∈ P ↔ 𝔭.IsMaximal ∧ J ≤ 𝔭 := fun 𝔭 => Set.Finite.mem_toFinset _
  have hmax : ∀ j : P, j.1.IsMaximal := fun j => ((hP j.1).1 j.2).1
  have H' : ∀ i : P, ∃ uv : M × M, N • uv.1 = 0 ∧ N • uv.2 = 0 ∧ ∀ x : M, N • x = 0 →
      ∃ a b : 𝓞 F, x - a • uv.1 - b • uv.2 ∈ i.1 • T := by
    intro i
    have hi := (hP i.1).1 i.2
    obtain ⟨u, v, hu, hv, hx⟩ :=
      H i.1 hi.1 ((Ideal.span_singleton_le_iff_mem _).mp hi.2)
    exact ⟨(u, v), hu, hv, hx⟩
  choose uv huv1 huv2 hgen using H'
  have hc : ∀ i : P, ∃ c : 𝓞 F, c - 1 ∈ i.1 ∧ ∀ j : P, j ≠ i → c ∈ j.1 := by
    intro i
    have htop : i.1 ⊔ ∏ j ∈ Finset.univ.erase i, j.1 = ⊤ := by
      apply Ideal.sup_prod_eq_top
      intro j hj
      exact (hmax i).coprime_of_ne (hmax j)
        (fun h => (Finset.ne_of_mem_erase hj) (Subtype.ext h.symm))
    have h1 : (1 : 𝓞 F) ∈ i.1 ⊔ ∏ j ∈ Finset.univ.erase i, j.1 := htop ▸ Submodule.mem_top
    obtain ⟨a, ha, k, hk, hak⟩ := Submodule.mem_sup.mp h1
    refine ⟨k, ?_, fun j hj => ?_⟩
    · have hk1 : k - 1 = -a := by rw [← hak]; ring
      rw [hk1]; exact i.1.neg_mem ha
    · exact (Ideal.prod_le_inf.trans
        (Finset.inf_le (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩))) hk
  choose c hc1 hc2 using hc
  have hcd : ∀ i j : P, c j - (if j = i then 1 else 0) ∈ i.1 := by
    intro i j
    by_cases h : j = i
    · subst h; simpa using hc1 j
    · simpa [h] using hc2 j i (fun e => h e.symm)
  have gl : ∀ (i : P) (w : P → M), (∀ j, w j ∈ T) → ∑ j, c j • w j - w i ∈ i.1 • T := by
    intro i w hw
    have hsum : ∑ j, c j • w j - w i = ∑ j, (c j - if j = i then 1 else 0) • w j := by
      simp [sub_smul, Finset.sum_sub_distrib, ite_smul]
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul (hcd i j) (hw j)
  have huT : ∀ j, (uv j).1 ∈ T := fun j => (hT _).2 (huv1 j)
  have hvT : ∀ j, (uv j).2 ∈ T := fun j => (hT _).2 (huv2 j)
  set p : Fin 2 → M := ![∑ j, c j • (uv j).1, ∑ j, c j • (uv j).2] with hpdef
  have hp0 : p 0 = ∑ j, c j • (uv j).1 := rfl
  have hp1 : p 1 = ∑ j, c j • (uv j).2 := rfl
  have hpT : ∀ i, p i ∈ T := by
    intro i
    fin_cases i
    · exact Submodule.sum_mem _ fun j _ => T.smul_mem _ (huT j)
    · exact Submodule.sum_mem _ fun j _ => T.smul_mem _ (hvT j)
  set S := Submodule.span (𝓞 F) (Set.range p) with hSdef
  have hloc : ∀ i : P, ∀ x ∈ T, ∃ a b : 𝓞 F, x - a • p 0 - b • p 1 ∈ i.1 • T := by
    intro i x hx
    obtain ⟨a, b, hab⟩ := hgen i x ((hT x).1 hx)
    refine ⟨a, b, ?_⟩
    have he : x - a • p 0 - b • p 1 = (x - a • (uv i).1 - b • (uv i).2)
        - a • (p 0 - (uv i).1) - b • (p 1 - (uv i).2) := by
      simp only [smul_sub]; abel
    rw [he]
    refine Submodule.sub_mem _ (Submodule.sub_mem _ hab (Submodule.smul_mem _ _ ?_))
      (Submodule.smul_mem _ _ ?_)
    · exact gl i (fun j => (uv j).1) huT
    · exact gl i (fun j => (uv j).2) hvT
  have hTfg : T.FG := by
    have hTset : (T : Set M) = {x : M | N • x = 0} := Set.ext hT
    have hfs : (T : Set M).Finite := by
      rw [hTset]; exact Set.finite_coe_iff.mp hfin
    exact Submodule.fg_def.mpr ⟨T, hfs, Submodule.span_eq T⟩
  set N' := T.map S.mkQ with hN'def
  have hN'fg : N'.FG := hTfg.map _
  have hprime : ∀ i : P, N' ≤ i.1 • N' := by
    rintro i _ ⟨x, hx, rfl⟩
    obtain ⟨a, b, hab⟩ := hloc i x hx
    have hq : S.mkQ x = S.mkQ (x - a • p 0 - b • p 1) := by
      simp only [Submodule.mkQ_apply]
      rw [Submodule.Quotient.eq]
      have : x - (x - a • p 0 - b • p 1) = a • p 0 + b • p 1 := by abel
      rw [this]
      exact S.add_mem (S.smul_mem _ (Submodule.subset_span ⟨0, rfl⟩))
        (S.smul_mem _ (Submodule.subset_span ⟨1, rfl⟩))
    rw [hq, hN'def, ← Submodule.map_smul'']
    exact Submodule.mem_map_of_mem hab
  have hprod : ∀ s : Finset P, N' ≤ (∏ i ∈ s, i.1) • N' := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.prod_insert hi, Submodule.mul_smul]
      exact (hprime i).trans (Submodule.smul_mono le_rfl ih)
  have hjac : (∏ i : P, i.1) ≤ J.jacobson := by
    unfold Ideal.jacobson
    refine le_sInf ?_
    rintro m ⟨hJm, hm⟩
    have hmP : m ∈ P := (hP m).2 ⟨hm, hJm⟩
    exact Ideal.prod_le_inf.trans (Finset.inf_le (f := fun i : P => i.1) (Finset.mem_univ ⟨m, hmP⟩))
  have hJN' : J • N' = ⊥ := by
    rw [eq_bot_iff]
    refine Submodule.smul_le.mpr ?_
    rintro r hr _ ⟨x, hx, rfl⟩
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    have hx0 : (N : 𝓞 F) • x = 0 := (Submodule.mem_torsionBy_iff _ _).mp hx
    rw [mul_smul, ← LinearMap.map_smul, hx0, map_zero, smul_zero]
    exact Submodule.zero_mem _
  have hN'bot : N' = ⊥ := by
    rw [Submodule.eq_smul_of_le_smul_of_le_jacobson hN'fg (hprod Finset.univ) hjac, hJN']
  have hTS : T ≤ S := by
    intro x hx
    have hmem : S.mkQ x ∈ N' := Submodule.mem_map_of_mem hx
    rw [hN'bot, Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmem
    exact hmem
  refine ⟨p, fun i => (hT _).1 (hpT i), fun y hy => ?_⟩
  have hyS : y ∈ S := hTS ((hT y).2 hy)
  obtain ⟨f, hf⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hyS
  refine ⟨f 0, f 1, ?_⟩
  rw [← hf, Fin.sum_univ_two]
end GlobalTheory

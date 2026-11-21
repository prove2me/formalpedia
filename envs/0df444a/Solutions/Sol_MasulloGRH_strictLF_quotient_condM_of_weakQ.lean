-- Prove2me | solution 1 for MasulloGRH.strictLF_quotient_condM_of_weakQ
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:08:15.235076+00:00
-- url     : https://prove2.me/submissions/462a64e5-8c40-4a14-ae3c-aaad522f82bc

import Theorems.Thm_MasulloGRH_strictLF_hlcs_and_closed_steps
import Theorems.Thm_MasulloGRH_nuclearFrechet_quotient_bounded_compact_closure
import Definitions.Def_MasulloGRH_LocallyConvex
open Set Filter Topology Bornology
open scoped Pointwise
open MasulloGRH

theorem solution
    (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hwQ : ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ nhds (0 : X n), ∀ k : ℕ, m ≤ k →
      ∀ W ∈ nhds (0 : X m), ∃ U' ∈ nhds (0 : X k), ∃ r : ℝ, 0 < r ∧
        ∀ x ∈ U, ∀ y ∈ U', ((x : E) - (y : E)) ∈ V →
          ∃ w ∈ W, ((x : E) - (r : ℂ) • (w : E)) ∈ V) :
    ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ nhds (0 : X n), ∀ k : ℕ, m ≤ k →
      ∀ W ∈ nhds (0 : X m), ∃ W' ∈ nhds (0 : X k),
        ∀ x ∈ U, ∀ y ∈ W', ((x : E) - (y : E)) ∈ V → ∃ w ∈ W, ((x : E) - (w : E)) ∈ V := by
  classical
  obtain ⟨hE,_⟩ := strictLF_hlcs_and_closed_steps E X hmono hexh (fun n => (hX n).1) htop
  obtain ⟨ι,hi,p,hp⟩ := hE.1
  have hadd := hp.topologicalAddGroup
  have hsm := hp.continuousSMul
  have hcl : IsClosed (V.toAddSubgroup : Set E) := hV
  have hT : T2Space (E ⧸ V) := inferInstanceAs (T2Space (E ⧸ V.toAddSubgroup))
  intro n
  obtain ⟨m,hnm,U,hU,hcomp⟩ := hwQ n
  refine ⟨m,hnm,U,hU,?_⟩
  intro k hmk W hW
  have hmetr := (hX k).1.2.2
  let L := V.comap (X m).subtype
  let P := X m ⧸ L
  let inc : X n →ₗ[ℂ] X m := Submodule.inclusion (hmono hnm)
  let j : P →ₗ[ℂ] (E ⧸ V) := Submodule.mapQ L V (X m).subtype le_rfl
  have hj : Continuous j := continuous_quot_lift _ (V.continuous_mkQ.comp continuous_subtype_val)
  have hj0 (z : P) (hz : j z = 0) : z = 0 := by
    obtain ⟨x,rfl⟩ := L.mkQ_surjective z
    exact (Submodule.Quotient.mk_eq_zero L).mpr ((Submodule.Quotient.mk_eq_zero V).mp hz)
  by_contra! hf
  let Z := {y : X k | ∃ x ∈ U, ((x:E) - (y:E)) ∈ V ∧ ∀ w ∈ W, ((x:E) - (w:E)) ∉ V}
  have hZ : 0 ∈ closure Z := by
    apply mem_closure_iff_nhds.mpr
    intro O hO
    obtain ⟨x,hx,y,hy,hxy,hn⟩ := hf O hO
    exact ⟨y,hy,x,hx,hxy,hn⟩
  obtain ⟨y,hy,ht⟩ := mem_closure_iff_seq_limit.mp hZ
  choose x hx hxy hnot using hy
  let z (l : ℕ) : P := L.mkQ (inc (x l))
  have hbounded : IsVonNBounded ℂ (range z) := by
    rw [(nhds_basis_balanced ℂ P).isVonNBounded_iff]
    intro D hD
    have hpre : L.mkQ ⁻¹' D ∈ 𝓝 0 := (L.continuous_mkQ.tendsto' 0 0 (map_zero _)) hD.1
    obtain ⟨O,hO,r,hr,hs⟩ := hcomp k hmk _ hpre
    obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually_mem hO)
    have htail : ∀ l ≥ N, z l ∈ (r:ℂ) • D := by
      intro l hl
      obtain ⟨w,hw,hew⟩ := hs (x l) (hx l) (y l) (hN l hl) (hxy l)
      refine ⟨L.mkQ w,hw,?_⟩
      change (r:ℂ) • L.mkQ w = z l
      rw [←map_smul]
      exact (Submodule.Quotient.eq L).mpr (show inc (x l) - (r:ℂ) • w ∈ L from hew) |>.symm
    have hfin : Absorbs ℂ D (z '' Iio N) :=
      (absorbent_nhds_zero hD.1).absorbs_finite ((finite_Iio N).image z)
    have hrest : Absorbs ℂ D ((r:ℂ) • D) := by
      apply Absorbs.of_norm
      exact ⟨‖(r:ℂ)‖,fun c hc => hD.2.smul_mono hc⟩
    refine (hfin.union hrest).mono_right ?_
    rintro _ ⟨l,rfl⟩
    rcases lt_or_ge l N with hl|hl
    · exact Or.inl ⟨l,hl,rfl⟩
    · exact Or.inr (htail l hl)
  have hLc : IsClosed (L : Set (X m)) := hV.preimage continuous_subtype_val
  have hK := nuclearFrechet_quotient_bounded_compact_closure (X m) (hX m).1 (hX m).2 L hLc _ hbounded
  have ht' : Tendsto (fun l => j (z l)) atTop (𝓝 0) := by
    have hy' : Tendsto (fun l => V.mkQ (y l:E)) atTop (𝓝 0) :=
      ((V.continuous_mkQ.comp continuous_subtype_val).tendsto' (0:X k) 0 (map_zero _)).comp ht
    exact hy'.congr (fun l => ((Submodule.Quotient.eq V).mpr (hxy l)).symm)
  have hzero : (0 : E ⧸ V) ∈ j '' closure (range z) :=
    (hK.image hj).isClosed.mem_of_tendsto ht' (Eventually.of_forall fun l =>
      ⟨z l,subset_closure (mem_range_self l),rfl⟩)
  obtain ⟨w,hw,hw0⟩ := hzero
  have hw' : (0 : P) ∈ closure (range z) := hj0 w hw0 ▸ hw
  have hnW : L.mkQ '' W ∈ 𝓝 (0 : P) := by
    simpa only [map_zero] using L.isOpenMap_mkQ.image_mem_nhds hW
  obtain ⟨a,ha,ha'⟩ := mem_closure_iff_nhds.mp hw' _ hnW
  obtain ⟨l,rfl⟩ := ha'
  obtain ⟨u,hu,he⟩ := ha
  exact hnot l u hu (show inc (x l) - u ∈ L from (Submodule.Quotient.eq L).mp he.symm)


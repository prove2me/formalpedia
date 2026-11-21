-- Prove2me | solution 1 for MasulloGRH.strictLF_quotient_condM_of_quotient_regular
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-21T00:05:40.835193+00:00
-- url     : https://prove2.me/submissions/34df3931-4865-48d0-940d-fd84f423785a

import Theorems.Thm_MasulloGRH_strictLF_quotient_sequentially_retractive_of_bounded_lifting
import Theorems.Thm_MasulloGRH_strictLF_quotient_regular_iff_bounded_lifting
import Theorems.Thm_MasulloGRH_bounded_in_strict_frechet_stages

open Set Filter Topology MasulloGRH

private theorem flatten_rows {Q : Type*} [Zero Q] [TopologicalSpace Q]
    (a : ℕ → ℕ → Q) (hrow : ∀ i, Tendsto (a i) atTop (nhds 0))
    (hunif : ∀ G ∈ nhds (0 : Q), ∀ᶠ i : ℕ in atTop, ∀ j, a i j ∈ G) :
    Tendsto (fun z : ℕ => a z.unpair.1 z.unpair.2) atTop (nhds 0) := by
  classical
  intro G hG
  obtain ⟨I, hI⟩ := eventually_atTop.mp (hunif G hG)
  choose J hJ using fun i => eventually_atTop.mp ((hrow i).eventually_mem hG)
  let M := max I ((Finset.range I).sup J)
  apply eventually_atTop.mpr
  refine ⟨(M+1)^2, fun z hz => ?_⟩
  let i := z.unpair.1
  let j := z.unpair.2
  by_cases hi : I ≤ i
  · exact hI i hi j
  by_cases hj : J i ≤ j
  · exact hJ i j hj
  have hi' : i < I := lt_of_not_ge hi
  have hMi : i ≤ M := hi'.le.trans (le_max_left ..)
  have hMj : j ≤ M := (lt_of_not_ge hj).le.trans
    ((Finset.le_sup (f := J) (Finset.mem_range.mpr hi')).trans (le_max_right ..))
  have hpair := Nat.pair_lt_max_add_one_sq i j
  have hmax : max i j ≤ M := max_le hMi hMj
  have hz' : i.pair j = z := Nat.pair_unpair z
  rw [hz'] at hpair
  exact False.elim ((not_lt_of_ge hz) (hpair.trans_le (by gcongr)))

theorem solution
    (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hreg : ∀ B : Set (E ⧸ V), Bornology.IsVonNBounded ℂ B →
      ∃ (n : ℕ) (A : Set (X n ⧸ V.comap (X n).subtype)), Bornology.IsVonNBounded ℂ A ∧
        B ⊆ Submodule.mapQ (V.comap (X n).subtype) V (X n).subtype le_rfl '' A) :
    ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ nhds (0 : X n), ∀ k : ℕ, m ≤ k →
      ∀ W ∈ nhds (0 : X m), ∃ W' ∈ nhds (0 : X k),
        ∀ x ∈ U, ∀ y ∈ W', ((x : E) - (y : E)) ∈ V → ∃ w ∈ W, ((x : E) - (w : E)) ∈ V  := by
  classical
  intro n
  obtain ⟨⟨⟨ι, _, p, hp⟩, _⟩, _⟩ := bounded_in_strict_frechet_stages E X hmono hexh
    (fun i => (hX i).1) htop
  let _ := hp.topologicalAddGroup
  let _ := hp.continuousSMul
  let _ (i : ℕ) : TopologicalSpace.MetrizableSpace (X i) := (hX i).1.2.2
  obtain ⟨U, hU⟩ := (nhds (0 : X n)).exists_antitone_basis
  let m (i : ℕ) := n+i
  by_contra! hbad
  choose k hk W hW hbadW using fun i =>
    hbad (m i) (Nat.le_add_right n i) (U i) (hU.mem i)
  choose A hA using fun i => (nhds (0 : X (k i))).exists_antitone_basis
  choose x hx y hy hxy hfail using fun i j => hbadW i (A i j) ((hA i).mem j)
  let a (i j : ℕ) : E ⧸ V := V.mkQ ((x i j : X n) : E)
  have hrow (i : ℕ) : Tendsto (a i) atTop (nhds 0) := by
    have h := (V.continuous_mkQ.comp (continuous_subtype_val (p := fun z => z ∈ X (k i)))).tendsto' 0 0 (by simp)
    have hy' := h.comp ((hA i).tendsto (hy i))
    apply hy'.congr
    intro j
    exact ((Submodule.Quotient.eq V).mpr (hxy i j)).symm
  have hglobal := flatten_rows a hrow (by
    intro G hG
    have hc : Continuous (fun z : X n => V.mkQ (z : E)) := V.continuous_mkQ.comp continuous_subtype_val
    have hpre : (fun z : X n => V.mkQ (z : E)) ⁻¹' G ∈ nhds 0 := hc.tendsto' 0 0 (by simp) hG
    exact (hU.eventually_subset hpre).mono (fun i hi j => hi (hx i j)))
  have hlift := (strictLF_quotient_regular_iff_bounded_lifting E X hmono hexh hX htop V hV).mpr hreg
  obtain ⟨i, v, hv, hv0⟩ := strictLF_quotient_sequentially_retractive_of_bounded_lifting
    E X hmono hexh hX htop V hV hlift _ hglobal
  let P (j : ℕ) := V.comap (X j).subtype
  let inc := Submodule.inclusion (hmono (show i ≤ m i from Nat.le_add_left i n))
  let T := Submodule.mapQ (P i) (P (m i)) inc (by intro z hz; exact hz)
  have hT : Continuous T := ((P i).isQuotientMap_mkQL.continuous_iff).mpr
    ((P (m i)).continuous_mkQ.comp (continuous_subtype_val.subtype_mk _))
  have hpair : Tendsto (Nat.pair i) atTop atTop := tendsto_atTop_mono (Nat.right_le_pair i) tendsto_id
  have hzero := (hT.tendsto' 0 0 T.map_zero).comp (hv0.comp hpair)
  have hnb : (P (m i)).mkQ '' W i ∈ nhds 0 := by
    simpa using (P (m i)).isOpenMap_mkQ.image_mem_nhds (hW i)
  obtain ⟨j, w, hw, heq⟩ := (hzero.eventually_mem hnb).exists
  apply hfail i j w hw
  apply (Submodule.Quotient.eq V).mp
  have hcomm (z : X i ⧸ P i) : Submodule.mapQ (P (m i)) V (X (m i)).subtype le_rfl (T z) =
      Submodule.mapQ (P i) V (X i).subtype le_rfl z := by
    obtain ⟨b, rfl⟩ := (P i).mkQ_surjective z
    rfl
  calc
    V.mkQ ((x i j : X n) : E) = Submodule.mapQ (P i) V (X i).subtype le_rfl (v (i.pair j)) := by
      simpa [a, Nat.unpair_pair] using (hv (i.pair j)).symm
    _ = Submodule.mapQ (P (m i)) V (X (m i)).subtype le_rfl (T (v (i.pair j))) := (hcomm _).symm
    _ = V.mkQ (w : E) := congrArg (Submodule.mapQ (P (m i)) V (X (m i)).subtype le_rfl) heq.symm

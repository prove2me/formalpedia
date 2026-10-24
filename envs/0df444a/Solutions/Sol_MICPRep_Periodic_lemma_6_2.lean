-- Prove2me | solution 1 for MICPRep.Periodic.lemma_6_2
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T08:31:26.364392+00:00
-- url     : https://prove2.me/submissions/472e0093-111b-4b3f-a718-c06275f7a9a0

import Mathlib
import Definitions.Def_MICPRep_Periodic_Setting
import Theorems.Thm_MICPRep_Periodic_proposition_4_2
import Theorems.Thm_MICPRep_Periodic_lemma_6_12
import Theorems.Thm_MICPRep_Periodic_lemma_6_13

/- Complete task-local helper bodies from BoundedBinary.lean. -/

namespace MICPRep.Periodic.Trichotomy

lemma bounded_lattice_finite {d : ℕ} {I : Set (Fin d → ℝ)} (hI : Bornology.IsBounded I) :
    (I ∩ intLattice d).Finite := by
  let f : (Fin d → ℤ) → Fin d → ℝ := fun z i => (z i : ℝ)
  have hf : Topology.IsClosedEmbedding f :=
    Topology.IsClosedEmbedding.piMap fun _ => Int.isClosedEmbedding_coe_real
  have hfin : (f ⁻¹' closure I).Finite :=
    (hf.isProperMap.isCompact_preimage hI.isCompact_closure).finite_of_discrete
  apply (hfin.image f).subset
  rintro z ⟨hz, a, rfl⟩
  exact ⟨a, subset_closure hz, rfl⟩

/-- Finite lattice slices are a finite family of nonempty closed convex lifts. -/
lemma binary_of_finite_lattice {n p d : ℕ} {M : Set (Ambient n p d)} {S : Set (Pt n)}
    (hM : Induces M S) (hfin : (indexSet M ∩ intLattice d).Finite) : IsBinaryMICPR S := by
  classical
  let J := ↥(indexSet M ∩ intLattice d)
  let : Fintype J := hfin.fintype
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let A : J → Set (Pt n × (Fin p → ℝ)) := fun z => {w | (w.1, w.2, z.val) ∈ M}
  apply (MICPRep.Periodic.proposition_4_2 S).1.mpr
  refine ⟨p, Fintype.card J, fun i => A (e.symm i), ?_, ?_⟩
  · intro i
    refine ⟨?_, hM.1.preimage (continuous_fst.prodMk (continuous_snd.prodMk continuous_const)), ?_⟩
    · rcases (e.symm i).property.1 with ⟨⟨x, y, z⟩, hm, hz⟩
      exact ⟨(x, y), by change (x, y, (e.symm i).val) ∈ M; simpa only [← hz] using hm⟩
    · intro w hw w' hw' a b ha hb hab
      have hm := hM.2.1 hw hw' ha hb hab
      change (a • w.1 + b • w'.1, a • w.2 + b • w'.2, (e.symm i).val) ∈ M
      simpa only [Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hab, one_smul] using hm
  · ext x
    constructor
    · intro hx
      obtain ⟨y, z, hzZ, hm⟩ := (hM.2.2 x).mp hx
      have hz : z ∈ indexSet M ∩ intLattice d := ⟨⟨(x, y, z), hm, rfl⟩, hzZ⟩
      refine Set.mem_iUnion.mpr ⟨e ⟨z, hz⟩, (x, y), ?_, rfl⟩
      simpa only [Equiv.symm_apply_apply] using (show (x, y) ∈ A ⟨z, hz⟩ from hm)
    · intro hx
      obtain ⟨i, w, hw, rfl⟩ := Set.mem_iUnion.mp hx
      exact (hM.2.2 w.1).mpr ⟨w.2, (e.symm i).val, (e.symm i).property.2, hw⟩

lemma bounded_binary {n p d : ℕ} {M : Set (Ambient n p d)} {S : Set (Pt n)}
    (hM : Induces M S) (hI : Bornology.IsBounded (indexSet M)) : IsBinaryMICPR S :=
  binary_of_finite_lattice hM (bounded_lattice_finite hI)

end MICPRep.Periodic.Trichotomy

/- Complete task-local helper bodies from ZeroLine.lean. -/

namespace MICPRep.Periodic.Trichotomy

open Set Filter
open scoped Topology

variable {n p d : ℕ} {M : Set (Ambient n p d)}

def lineFiber (M : Set (Ambient n p d)) (z r : Fin d → ℝ) : Set (Pt n) :=
  ⋃ w ∈ {w | ∃ t : ℝ, w = z + t • r} ∩ indexSet M, zProj M w

lemma fiber_nonempty {z : Fin d → ℝ} (hz : z ∈ indexSet M) :
    (zProj M z).Nonempty := by
  rcases hz with ⟨⟨x, y, w⟩, h, rfl⟩
  exact ⟨x, y, h⟩

lemma lattice_add_nsmul {z r : Fin d → ℝ} (hz : z ∈ intLattice d)
    (hr : r ∈ intLattice d) (k : ℕ) : z + (k : ℝ) • r ∈ intLattice d := by
  rcases hz with ⟨z, rfl⟩
  rcases hr with ⟨r, rfl⟩
  refine ⟨fun i => z i + (k : ℤ) * r i, ?_⟩
  ext i
  simp

-- These elementary closure-combination bodies are reproduced from the checked
-- micp-asymptotic geometry proof; no theorem-internal helper is imported.
lemma fiber_combo_closure_right (hM : Convex ℝ M) {z w : Fin d → ℝ} {x y : Pt n}
    (hx : x ∈ zProj M z) (hy : y ∈ closure (zProj M w))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • x + b • y ∈ closure (zProj M (a • z + b • w)) := by
  have hc : IsClosed {y : Pt n | a • x + b • y ∈
      closure (zProj M (a • z + b • w))} :=
    isClosed_closure.preimage (by fun_prop)
  apply closure_minimal (t := {y : Pt n | a • x + b • y ∈
      closure (zProj M (a • z + b • w))}) ?_ hc hy
  intro y hy
  obtain ⟨x', hx'⟩ := hx
  obtain ⟨y', hy'⟩ := hy
  exact subset_closure ⟨a • x' + b • y', hM hx' hy' ha hb hab⟩

/-- Zero drift carries even a negative-time fiber into every sufficiently late fiber. -/
lemma line_later_closure (hM : Convex ℝ M) {z r : Fin d → ℝ} {x₀ x : Pt n}
    (hbase : ∀ L : ℝ, 0 < L → x₀ ∈ closure (zProj M (z + L • r)))
    {t k : ℝ} (hk : 0 ≤ k) (htk : t < k) (hx : x ∈ zProj M (z + t • r)) :
    x ∈ closure (zProj M (z + k • r)) := by
  have hc : Tendsto (fun b : ℝ => (1-b) • x + b • x₀) (𝓝[>] 0) (𝓝 x) := by
    have hh : Continuous (fun b : ℝ => (1-b) • x + b • x₀) := by fun_prop
    simpa using (hh.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  apply isClosed_closure.mem_of_tendsto hc
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with b hb
  have hdiv : k - t < (k - t) / b := (lt_div_iff₀ hb.1).mpr (by nlinarith [hb.2])
  have hL : 0 < t + (k-t)/b := by linarith
  have heq : (1-b) • (z+t•r) + b • (z+(t+(k-t)/b)•r) = z+k•r := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp [hb.1.ne']
    ring
  exact heq ▸ fiber_combo_closure_right hM hx (hbase _ hL)
    (by linarith [hb.2]) hb.1.le (by ring)

lemma zero_line_properties {S : Set (Pt n)} (hM : Induces M S)
    {z r : Fin d → ℝ} (hz : z ∈ intLattice d ∩ indexSet M)
    (hrZ : r ∈ intLattice d) (hrI : r ∈ recCone (indexSet M))
    (hzero : ∀ t : ℝ, 0 < t → ∀ x ∈ zProj M z, x ∈ closure (zProj M (z + t • r))) :
    Metric.ediam (lineFiber M z r) ≤ micpDiam M ∧ lineFiber M z r ⊆ closure S := by
  obtain ⟨x₀, hx₀⟩ := fiber_nonempty hz.2
  have hbase := fun t ht => hzero t ht x₀ hx₀
  have hdiam (k : ℕ) : Metric.ediam (closure (zProj M (z + (k : ℝ) • r))) ≤ micpDiam M := by
    rw [Metric.ediam_closure]
    exact le_iSup_of_le (z + (k : ℝ) • r)
      (le_iSup_of_le ⟨hrI z hz.2 k (by positivity), lattice_add_nsmul hz.1 hrZ k⟩ le_rfl)
  constructor
  · apply Metric.ediam_le
    intro x hx y hy
    simp only [lineFiber, mem_iUnion, mem_inter_iff, mem_ofPred_eq] at hx hy
    obtain ⟨_, ⟨⟨t, rfl⟩, _⟩, hx⟩ := hx
    obtain ⟨_, ⟨⟨s, rfl⟩, _⟩, hy⟩ := hy
    obtain ⟨k, hk⟩ := exists_nat_gt (max t s)
    have htk : t < (k : ℝ) := (le_max_left _ _).trans_lt hk
    have hsk : s < (k : ℝ) := (le_max_right _ _).trans_lt hk
    exact (Metric.edist_le_ediam_of_mem (line_later_closure hM.2.1 hbase (by positivity) htk hx)
      (line_later_closure hM.2.1 hbase (by positivity) hsk hy)).trans (hdiam k)
  · intro x hx
    simp only [lineFiber, mem_iUnion, mem_inter_iff, mem_ofPred_eq] at hx
    obtain ⟨_, ⟨⟨t, rfl⟩, _⟩, hx⟩ := hx
    obtain ⟨k, hk⟩ := exists_nat_gt t
    apply closure_mono (s := zProj M (z + (k : ℝ) • r)) ?_
      (line_later_closure hM.2.1 hbase (by positivity) hk hx)
    intro y hy
    obtain ⟨y', hy'⟩ := hy
    exact (hM.2.2 y).mpr ⟨y', z + (k : ℝ) • r, lattice_add_nsmul hz.1 hrZ k, hy'⟩

end MICPRep.Periodic.Trichotomy

/- Complete task-local helper bodies from Reduction.lean. -/

namespace MICPRep.Periodic.Trichotomy

lemma zero_reduction {n p d' : ℕ} (M : Set (Ambient n p (d' + 1))) (S : Set (Pt n))
    (hM : IsRationalFormulation M S) (hS : S.Nonempty) (r : Fin (d' + 1) → ℝ)
    (hrZ : r ∈ intLattice (d' + 1)) (hrI : r ∈ recCone (indexSet M)) (hr0 : r ≠ 0)
    (hzero : ∀ t : ℝ, 0 < t → ∀ z ∈ intLattice (d' + 1) ∩ indexSet M,
      ∀ x ∈ zProj M z, x ∈ closure (zProj M (z + t • r))) :
    ∃ (p' : ℕ) (Mt : Set (Ambient n p' d')) (St : Set (Pt n)),
      IsRationalFormulation Mt St ∧ St.Nonempty ∧ micpDiam Mt ≤ micpDiam M ∧
      S ⊆ St ∧ St ⊆ closure St ∧ closure St ⊆ closure S := by
  obtain ⟨Mt, St, hMt, hslices, _⟩ := MICPRep.Periodic.lemma_6_12 M S hM r hrZ hrI hr0
  have hsub : S ⊆ St := by
    intro x hx
    obtain ⟨y, z, hzZ, hm⟩ := (hM.1.2.2 x).mp hx
    have hzI : z ∈ indexSet M := ⟨(x, y, z), hm, rfl⟩
    obtain ⟨zt, hzt, heq⟩ := (hslices (lineFiber M z r)).mpr ⟨z, ⟨hzZ, hzI⟩, rfl⟩
    have hxline : x ∈ lineFiber M z r := by
      apply Set.mem_iUnion.mpr ⟨z, ?_⟩
      apply Set.mem_iUnion.mpr ⟨⟨⟨0, by simp⟩, hzI⟩, ?_⟩
      exact ⟨y, hm⟩
    rw [heq] at hxline
    obtain ⟨yt, hyt⟩ := hxline
    exact (hMt.1.2.2 x).mpr ⟨yt, zt, hzt.2, hyt⟩
  have hclosure : St ⊆ closure S := by
    intro x hx
    obtain ⟨y, zt, hztZ, hm⟩ := (hMt.1.2.2 x).mp hx
    have hztI : zt ∈ indexSet Mt := ⟨(x, y, zt), hm, rfl⟩
    obtain ⟨z, hz, heq⟩ := (hslices (zProj Mt zt)).mp ⟨zt, ⟨hztI, hztZ⟩, rfl⟩
    have hxline : x ∈ lineFiber M z r := by rw [lineFiber, ← heq]; exact ⟨y, hm⟩
    exact (zero_line_properties hM.1 hz hrZ hrI (fun t ht => hzero t ht z hz)).2 hxline
  refine ⟨p + 1, Mt, St, hMt, hS.mono hsub, ?_, hsub, subset_closure,
    closure_minimal hclosure isClosed_closure⟩
  apply iSup_le
  intro zt
  apply iSup_le
  intro hzt
  obtain ⟨z, hz, heq⟩ := (hslices (zProj Mt zt)).mp ⟨zt, hzt, rfl⟩
  rw [heq]
  exact (zero_line_properties hM.1 hz hrZ hrI (fun t ht => hzero t ht z hz)).1

end MICPRep.Periodic.Trichotomy


open MICPRep.Periodic MICPRep.Periodic.Trichotomy
open scoped ENNReal Matrix

theorem solution {n p d : ℕ} (M : Set (Ambient n p d)) (S : Set (Pt n))
    (hM : IsRationalFormulation M S) (hS : S.Nonempty) (hD : micpDiam M < ⊤)
    (hint : (intrinsicInterior ℝ (IZ (indexSet M)) ∩ intLattice d).Nonempty) :
    IsBinaryMICPR S ∨ HasNearlyPeriodicFormulation S ∨
      ∃ d' : ℕ, d = d' + 1 ∧
        ∃ (p' : ℕ) (Mt : Set (Ambient n p' d')) (St : Set (Pt n)),
          IsRationalFormulation Mt St ∧ St.Nonempty ∧ micpDiam Mt ≤ micpDiam M ∧
          S ⊆ St ∧ St ⊆ closure St ∧ closure St ⊆ closure S := by
  have hidentity : ratAff (1 : Matrix (Fin d) (Fin d) ℚ) 0 = id := by
    funext z
    simp [ratAff, Matrix.map_one]
    rfl
  obtain hbounded | ⟨r, hrZ, hr0, hrI⟩ := hM.2 d 1 0
  · rw [hidentity, Set.image_id] at hbounded
    exact Or.inl (bounded_binary hM.1 hbounded)
  · rw [hidentity, Set.image_id] at hrI
    obtain ⟨u, hu, _⟩ := (MICPRep.Periodic.lemma_6_13 M S hM hD hint r hrZ hrI hr0).1
    by_cases hu0 : u = 0
    · have hzero : ∀ t : ℝ, 0 < t → ∀ z ∈ intLattice d ∩ indexSet M,
          ∀ x ∈ zProj M z, x ∈ closure (zProj M (z + t • r)) := by
        simpa only [hu0, smul_zero, add_zero] using hu
      cases d with
      | zero =>
          exact False.elim (hr0 (Subsingleton.elim r 0))
      | succ d' =>
          exact Or.inr (Or.inr ⟨d', rfl, zero_reduction M S hM hS r hrZ hrI hr0 hzero⟩)
    · apply Or.inr ∘ Or.inl
      refine ⟨p, d, M, hM.1, u, hu0, r, hrZ, hr0, hrI, ?_⟩
      intro k z hz x hx
      by_cases hk : k = 0
      · simpa only [hk, Nat.cast_zero, zero_smul, add_zero] using (subset_closure hx)
      · exact hu k (by exact_mod_cast Nat.pos_of_ne_zero hk) z hz x hx

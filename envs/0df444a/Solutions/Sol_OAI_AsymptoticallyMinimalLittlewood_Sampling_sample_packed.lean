-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Sampling.sample_packed
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:03:39.178917+00:00
-- url     : https://prove2.me/submissions/a83d1aec-b4f4-474d-9b91-02be33ebd46c

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/BlockSampling.lean:L230-L339
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Sampling.sample_packed. The node keeps its source
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
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks
import Definitions.Def_OAI_Analysis_Littlewood_DependentMoments
import Definitions.Def_OAI_Analysis_Littlewood_SlotGraph
import Definitions.Def_OAI_Analysis_Littlewood_SlotParameters
import Definitions.Def_OAI_Analysis_Littlewood_IntervalPacking
import Definitions.Def_OAI_Analysis_Littlewood_SamplingTail
import Definitions.Def_OAI_Analysis_Littlewood_SamplingEnergy
import Definitions.Def_OAI_Analysis_Littlewood_ModeSampling
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Cutoff_unit_cutoff
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Sampling_block_value_bound
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Sampling_mode_energy
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Sampling_mode_maximum

-- ---- from OAI.Analysis.Littlewood.BlockSampling ----
namespace OAI

universe uP uJ uI

namespace AsymptoticallyMinimalLittlewood.Cutoff
noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology ContDiff

theorem block_cutoffs {H : ℕ} (hH : 1≤H) {δ : ℝ} (hδ : 0<δ) :
    ∃ χ : Fin H → ℝ → ℝ,
      (∀ h, ContDiff ℝ ∞ (χ h)) ∧ (∀ h, HasCompactSupport (χ h)) ∧
      (∀ h, tsupport (χ h)⊆Ioo ((h : ℝ)/H) (((h : ℝ)+1)/H)) ∧
      (∀ h x, 0≤χ h x ∧ χ h x≤1) ∧
      1-δ < ∑ h, ∫ x : ℝ, (χ h x)^2 := by
  obtain ⟨g,hgs,hgc,⟨α,hα0,hα,hga⟩,hgb,hgm⟩ := unit_cutoff hδ
  have hH0 : 0<(H : ℝ) := by exact_mod_cast (show 0<H by omega)
  let χ (h : Fin H) (x : ℝ) := g ((H : ℝ)*x-((h : ℝ)+1/2))
  have hcomp (h : Fin H) : HasCompactSupport (χ h) := by
    exact hgc.comp_homeomorph ((Homeomorph.mulLeft₀ (H : ℝ) hH0.ne').trans
      (Homeomorph.subRight ((h : ℝ)+1/2)))
  have hsupp (h : Fin H) : tsupport (χ h)⊆Ioo ((h : ℝ)/H) (((h : ℝ)+1)/H) := by
    intro x hx
    have hh : (H : ℝ)*x-((h : ℝ)+1/2)∈tsupport g :=
      tsupport_comp_subset_preimage g (f := fun x : ℝ ↦ (H : ℝ)*x-((h : ℝ)+1/2)) (by fun_prop) hx
    obtain ⟨hx1,hx2⟩ := hga hh
    constructor
    · rw [div_lt_iff₀ hH0]; nlinarith
    · rw [lt_div_iff₀ hH0]; nlinarith
  have hint (h : Fin H) : (∫ x : ℝ, (χ h x)^2)=(∫ x : ℝ, g x^2)/(H : ℝ) := by
    change (∫ x : ℝ, g ((H : ℝ)*x-((h : ℝ)+1/2))^2)=_
    rw [Measure.integral_comp_mul_left (fun x : ℝ ↦ g (x-((h : ℝ)+1/2))^2) (H : ℝ),
      integral_sub_right_eq_self (fun x : ℝ ↦ g x^2),abs_inv,abs_of_pos hH0]
    simp only [smul_eq_mul]
    ring
  refine ⟨χ,(fun h ↦ hgs.comp (by fun_prop)),hcomp,hsupp,(fun h x ↦ hgb _),?_⟩
  simp_rw [hint]
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    mul_div_cancel₀ _ hH0.ne'] using hgm

lemma block_support_unit {H : ℕ} (hH : 1≤H) (h : Fin H) {χ : ℝ → ℝ}
    (hs : tsupport χ⊆Ioo ((h : ℝ)/H) (((h : ℝ)+1)/H)) :
    tsupport χ⊆Ioo (0:ℝ) 1 := by
  intro x hx
  obtain ⟨h1,h2⟩ := hs hx
  have hH0 : 0<(H : ℝ) := by exact_mod_cast (show 0<H by omega)
  have hh0 : 0≤(h : ℝ) := by positivity
  have hh1 : (h : ℝ)+1≤H := by exact_mod_cast (show h.val+1≤H by omega)
  exact ⟨lt_of_le_of_lt (div_nonneg hh0 hH0.le) h1,
    lt_of_lt_of_le h2 ((div_le_one hH0).mpr hh1)⟩

lemma blocks_disjoint {H : ℕ} (hH : 1≤H) (χ : Fin H → ℝ → ℝ)
    (hs : ∀ h, tsupport (χ h)⊆Ioo ((h : ℝ)/H) (((h : ℝ)+1)/H))
    {i j : Fin H} (hij : i≠j) (x : ℝ) : χ i x*χ j x=0 := by
  apply mul_eq_zero.mpr
  by_contra hn
  push Not at hn
  have hi := hs i (subset_tsupport _ hn.1)
  have hj := hs j (subset_tsupport _ hn.2)
  have hH0 : 0<(H : ℝ) := by exact_mod_cast (show 0<H by omega)
  have h1 := (div_lt_iff₀ hH0).mp hi.1
  have h2 := (lt_div_iff₀ hH0).mp hi.2
  have h3 := (div_lt_iff₀ hH0).mp hj.1
  have h4 := (lt_div_iff₀ hH0).mp hj.2
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with ht | ht
  · have hh : (i : ℝ)+1 ≤ (j : ℝ) := by exact_mod_cast (show i.val+1≤j.val by omega)
    linarith
  · have hh : (j : ℝ)+1 ≤ (i : ℝ) := by exact_mod_cast (show j.val+1 ≤ i.val by omega)
    linarith

end
end AsymptoticallyMinimalLittlewood.Cutoff

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators

lemma circle_int_zero (l : ℤ) : ((l : ℝ) : UnitAddCircle)=0 :=
  (AddCircle.coe_eq_zero_iff (1:ℝ)).mpr ⟨l,by simp⟩

lemma center_mem_interval (a : UnitAddCircle) {w : ℝ} (hw : 0≤w) :
    a∈circleInterval a w := ⟨0,by simpa using (div_nonneg hw (by norm_num : (0:ℝ)≤2)),by simp⟩

lemma disjoint_centers_noninteger {a b u v : ℝ} (hu : 0≤u) (hv : 0≤v)
    (hd : Disjoint (circleInterval (a : UnitAddCircle) u) (circleInterval (b : UnitAddCircle) v)) :
    ∀ l : ℤ, (l : ℝ)≠a-b := by
  intro l hl
  have he : (a : UnitAddCircle)=(b : UnitAddCircle) := by
    apply sub_eq_zero.mp
    rw [← AddCircle.coe_sub,← hl,circle_int_zero]
  exact Set.disjoint_left.mp hd (center_mem_interval _ hu) (he ▸ center_mem_interval _ hv)

lemma block_center_distance {H : ℕ} (hH : 1≤H) (h : Fin H) {x : ℝ}
    (hx : x∈Set.Ioo ((h : ℝ)/H) (((h : ℝ)+1)/H)) :
    |x-((h : ℝ)+1/2)/H|<1/(2*H) := by
  have hH0 : 0<(H : ℝ) := by exact_mod_cast (show 0<H by omega)
  have he1 : (h : ℝ)/H-((h : ℝ)+1/2)/H= -(1/(2*H)) := by ring
  have he2 : ((h : ℝ)+1)/H-((h : ℝ)+1/2)/H=1/(2*H) := by ring
  rw [abs_lt]
  constructor <;> linarith only [hx.1,hx.2,he1,he2]

lemma stationary_in_interval {H : ℕ} (hH : 1≤H) (h : Fin H) (a t lam : ℝ)
    (hlam : lam≠0) (l : ℤ) {g : ℝ → ℂ}
    (hg : tsupport g⊆Set.Ioo ((h : ℝ)/H) (((h : ℝ)+1)/H))
    (hn : g (((l : ℝ)-(a-lam*((h : ℝ)+1/2)/H+t))/lam)≠0) :
    (-t : UnitAddCircle)∈circleInterval (a : UnitAddCircle) (|lam|/H) ∧
      |(l : ℝ)-t-a|< |lam|/(2*H) := by
  have hx := block_center_distance hH h (hg (subset_tsupport _ hn))
  have he : ((l : ℝ)-(a-lam*((h : ℝ)+1/2)/H+t))/lam-((h : ℝ)+1/2)/H=
      ((l : ℝ)-t-a)/lam := by field_simp; ring
  rw [he,abs_div] at hx
  have hab : |(l : ℝ)-t-a|< |lam|/(2*H) := by
    have hh := (div_lt_iff₀ (abs_pos.mpr hlam)).mp hx
    simpa only [one_div_mul_eq_div] using hh
  refine ⟨⟨(l : ℝ)-t-a,by simpa only [div_div,mul_comm (H : ℝ) 2] using hab.le,?_⟩,hab⟩
  rw [← AddCircle.coe_add,show a+((l : ℝ)-t-a)=(l : ℝ)-t by ring,
    AddCircle.coe_sub,circle_int_zero,zero_sub]

lemma stationary_unique {P : Type uP} {H : ℕ} (hH : 1≤H)
    (block : P → Fin H) (g : P → ℝ → ℂ) (a lam : P → ℝ)
    (hlam : ∀ i, lam i≠0) (hwidth : ∀ i, |lam i|/(H : ℝ)<1)
    (hgi : ∀ i, tsupport (g i)⊆Set.Ioo ((block i : ℝ)/H) (((block i : ℝ)+1)/H))
    (hd : ∀ i j, i≠j → Disjoint (circleInterval (a i : UnitAddCircle) (|lam i|/H))
      (circleInterval (a j : UnitAddCircle) (|lam j|/H))) :
    ∀ t : ℝ, ∀ i j : P, ∀ l m : ℤ,
      g i (((l : ℝ)-(a i-lam i*((block i : ℝ)+1/2)/H+t))/lam i)≠0 →
      g j (((m : ℝ)-(a j-lam j*((block j : ℝ)+1/2)/H+t))/lam j)≠0 →
      i=j ∧ l=m := by
  intro t i j l m hi hj
  have h1 := stationary_in_interval hH (block i) (a i) t (lam i) (hlam i) l (hgi i) hi
  have h2 := stationary_in_interval hH (block j) (a j) t (lam j) (hlam j) m (hgi j) hj
  have hij : i=j := by
    by_contra hn
    exact Set.disjoint_left.mp (hd i j hn) h1.1 h2.1
  subst j
  refine ⟨rfl,?_⟩
  have hm : |((l-m : ℤ) : ℝ)|<1 := by
    have hh := abs_sub ((l : ℝ)-t-a i) ((m : ℝ)-t-a i)
    rw [show (l : ℝ)-t-a i-((m : ℝ)-t-a i)=(l : ℝ)-m by ring] at hh
    push_cast
    calc
      _ ≤ |(l : ℝ)-t-a i|+|(m : ℝ)-t-a i| := hh
      _ < |lam i|/H := by linarith [h1.2,h2.2,show |lam i|/(2*H)= (|lam i|/H)/2 by ring]
      _ < 1 := hwidth i
  have hz : |l-m|<1 := by exact_mod_cast hm
  have := abs_lt.mp hz
  omega

end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open scoped BigOperators ComplexConjugate
open Complex UnitAddTorus
namespace Sampling
open QuadraticTail

lemma mFourier_lift {J : Type uJ} [Fintype J] (a : J → ℤ) (y : J → ℝ) :
    mFourier a (fun j ↦ (y j : UnitAddCircle))=
      realPhase (2*Real.pi*∑ j, (a j : ℝ)*y j) := by
  simp only [mFourier,ContinuousMap.coe_mk,fourier_coe_apply]
  rw [← Complex.exp_sum]
  unfold realPhase
  congr 1
  push_cast
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma mFourier_chirp {J : Type uJ} [Fintype J] (a : J → ℤ) (θ v : J → ℝ)
    {N : ℕ} (hN : 0<N) (k : Fin N) (x : ℝ) :
    mFourier a (fun j ↦ (((k : ℝ)*θ j+(N : ℝ)/2*v j*((k : ℝ)/N-x)^2 : ℝ) : UnitAddCircle))=
      realPhase (2*Real.pi*N*((∑ j, (a j : ℝ)*v j)*x^2/2))*
        phase ((∑ j, (a j : ℝ)*v j)/N)
          (-((∑ j, (a j : ℝ)*θ j)-(∑ j, (a j : ℝ)*v j)*x)) k := by
  rw [mFourier_lift]
  have hNr : (N : ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hsum : (∑ j, (a j : ℝ)*((k : ℝ)*θ j+(N : ℝ)/2*v j*((k : ℝ)/N-x)^2))=
      (k : ℝ)*(∑ j, (a j : ℝ)*θ j)+(N : ℝ)/2*((k : ℝ)/N-x)^2*(∑ j, (a j : ℝ)*v j) := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum,realPhase,realPhase,phase,← Complex.exp_add]
  congr 1
  push_cast
  have hn : (N : ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  field_simp
  ring

end Sampling
end
end AsymptoticallyMinimalLittlewood

namespace AsymptoticallyMinimalLittlewood.Sampling
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Complex QuadraticTail UnitAddTorus Packing Cutoff

/-- Exact fixed-block sampler for a packed real trigonometric polynomial. -/
theorem sample_packed {I J : Type} [Fintype I] [Fintype J]
    (a : I → J → ℤ) (c : I → ℂ) (v : J → ℝ) {H : ℕ} (hH : 1≤H)
    (θ : Fin H → J → ℝ)
    (hreal : ∀ y : J → UnitAddCircle, (∑ i, c i*mFourier (a i) y).im=0)
    (hbound : ∀ y : J → UnitAddCircle, ‖∑ i, c i*mFourier (a i) y‖≤1)
    (hlam : ∀ i, (∑ j, (a i j : ℝ)*v j)≠0)
    (hwidth : ∀ i, |∑ j, (a i j : ℝ)*v j|/(H : ℝ)<1)
    (hpack : ∀ h h' : Fin H, ∀ i i' : I, (h,i)≠(h',i') →
      Disjoint (circleInterval (((∑ j, (a i j : ℝ)*θ h j : ℝ)) : UnitAddCircle)
        (|∑ j, (a i j : ℝ)*v j|/H))
      (circleInterval (((∑ j, (a i' j : ℝ)*θ h' j : ℝ)) : UnitAddCircle)
        (|∑ j, (a i' j : ℝ)*v j|/H)))
    {K δ : ℝ} (hK : 0≤K) (hδ : 0<δ)
    (hc : ∀ i, ‖c i‖/Real.sqrt |∑ j, (a i j : ℝ)*v j|≤K) :
    ∃ X : (N : ℕ) → Fin N → ℝ, ∃ L C : ℝ,
      0≤C ∧ (1-δ)*(∑ i, ‖c i‖^2)≤L ∧
      (∀ N : ℕ, 1≤N → ∀ k, |X N k|≤1) ∧
      Tendsto (fun N : ℕ ↦ (∑ k : Fin N, (X N k)^2)/(N : ℝ)) atTop (𝓝 L) ∧
      ∀ N : ℕ, 1≤N → ∀ t∈Set.Icc (0:ℝ) 1,
        ‖(1/(Real.sqrt N : ℂ))*∑ k : Fin N, (X N k : ℂ)*realPhase (2*Real.pi*t*k)‖≤K+C/N := by
  classical
  obtain ⟨χ,hχs,hχc,hχi,hχb,hχm⟩ := block_cutoffs hH hδ
  let lam₀ (i : I) := ∑ j, (a i j : ℝ)*v j
  let α (p : Fin H × I) := ∑ j, (a p.2 j : ℝ)*θ p.1 j
  let xstar (h : Fin H) := ((h : ℝ)+1/2)/H
  let lam (p : Fin H × I) := lam₀ p.2
  let b (p : Fin H × I) := α p-lam p*xstar p.1
  let d (p : Fin H × I) := lam p*(xstar p.1)^2/2
  let g (p : Fin H × I) (x : ℝ) : ℂ := (χ p.1 x : ℂ)
  let cp (p : Fin H × I) := c p.2
  have hgc (p : Fin H × I) : HasCompactSupport (g p) :=
    (hχc p.1).comp_left (show Complex.ofReal 0=0 by simp)
  have hgs (p : Fin H × I) : ContDiff ℝ ∞ (g p) :=
    Complex.ofRealCLM.contDiff.comp (hχs p.1)
  have hgb (p : Fin H × I) (x : ℝ) : ‖g p x‖≤1 := by
    simpa only [g,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hχb p.1 x).1] using (hχb p.1 x).2
  have hgis (p : Fin H × I) : tsupport (g p)⊆Set.Ioo ((p.1 : ℝ)/H) (((p.1 : ℝ)+1)/H) :=
    (tsupport_comp_subset (show Complex.ofReal 0=0 by simp) (χ p.1)).trans (hχi p.1)
  have hgi (p : Fin H × I) : tsupport (g p)⊆Set.Ioo (0:ℝ) 1 := by
    apply (tsupport_comp_subset (show Complex.ofReal 0=0 by simp) (χ p.1)).trans
    exact block_support_unit hH p.1 (hχi p.1)
  have hsparse := stationary_unique hH Prod.fst g α lam (fun p ↦ hlam p.2)
    (fun p ↦ hwidth p.2) hgis (fun p q hpq ↦ hpack p.1 q.1 p.2 q.2 hpq)
  obtain ⟨C,hC,hmax⟩ := mode_maximum g cp lam b d hgc hgs hgi hgb
    (fun p ↦ hlam p.2) hK (fun p ↦ hc p.2) (by
      simpa only [b,xstar,mul_div_assoc] using hsparse)
  have hfreq (p q : Fin H × I) (hpq : p≠q) :
      (lam p≠lam q ∨ ∀ l : ℤ, (l : ℝ)≠b p-b q) ∨ ∀ x, g p x*conj (g q x)=0 := by
    by_cases hh : p.1=q.1
    · left
      by_cases hl : lam p=lam q
      · right
        have hd := disjoint_centers_noninteger
          (div_nonneg (abs_nonneg (lam p)) (Nat.cast_nonneg H))
          (div_nonneg (abs_nonneg (lam q)) (Nat.cast_nonneg H))
          (hpack p.1 q.1 p.2 q.2 hpq)
        have he : b p-b q=α p-α q := by dsimp [b]; rw [hh,hl]; ring
        simpa only [he] using hd
      · exact Or.inl hl
    · right
      intro x
      have hh' := blocks_disjoint hH χ hχi hh x
      simp only [g,Complex.conj_ofReal,← Complex.ofReal_mul,hh',Complex.ofReal_zero]
  have henergy := mode_energy g cp lam b d hgc hgs hgi hgb hfreq
  let L := (∑ h : Fin H, ∫ x : ℝ, (χ h x)^2)*(∑ i, ‖c i‖^2)
  have hL : (∑ p : Fin H × I, ‖cp p‖^2*(∫ x : ℝ, ‖g p x‖^2))=L := by
    simp only [cp,g,Complex.norm_real,Real.norm_eq_abs,sq_abs,Fintype.sum_prod_type]
    simp only [L,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h _
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hL] at henergy
  let X (N : ℕ) (k : Fin N) := (modeSum g cp lam b d N k).re
  have hmode (N : ℕ) (hN : 1≤N) (k : Fin N) :
      modeSum g cp lam b d N k=
      ∑ h, (χ h ((k : ℝ)/N) : ℂ)*(∑ i, c i*mFourier (a i)
        (fun j ↦ (((k : ℝ)*θ h j+(N : ℝ)/2*v j*((k : ℝ)/N-xstar h)^2 : ℝ) : UnitAddCircle))) := by
    simp only [modeSum,Fintype.sum_prod_type,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    apply Finset.sum_congr rfl
    intro i _
    rw [mFourier_chirp (a i) (θ h) v (show 0<N by omega)]
    dsimp [g,cp,lam,lam₀,b,d,α]
    ring
  have hX (N : ℕ) (hN : 1≤N) (k : Fin N) : (X N k : ℂ)=modeSum g cp lam b d N k := by
    apply Complex.ext
    · rfl
    · simp only [Complex.ofReal_im,hmode N hN,Complex.im_sum,Complex.mul_im,
        Complex.ofReal_im,Complex.ofReal_re,hreal,mul_zero,zero_mul,add_zero,Finset.sum_const_zero]
  have hXb (N : ℕ) (hN : 1≤N) (k : Fin N) : |X N k|≤1 := by
    have hv := block_value_bound (fun h ↦ χ h ((k : ℝ)/N))
      (fun h ↦ ∑ i, c i*mFourier (a i)
        (fun j ↦ (((k : ℝ)*θ h j+(N : ℝ)/2*v j*((k : ℝ)/N-xstar h)^2 : ℝ) : UnitAddCircle)))
      (fun h ↦ hχb h _) (fun h ↦ hbound _) (fun i j hn ↦ blocks_disjoint hH χ hχi hn _)
    rw [← hmode N hN k,← hX N hN k,Complex.norm_real,Real.norm_eq_abs] at hv
    exact hv
  refine ⟨X,L,C,hC,mul_le_mul_of_nonneg_right hχm.le (Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)),hXb,?_,?_⟩
  · apply henergy.congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [← hX N hN k,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  · intro N hN t ht
    simpa only [hX N hN] using hmax N hN t ht

end
end AsymptoticallyMinimalLittlewood.Sampling

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Sampling
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Complex QuadraticTail UnitAddTorus Packing Cutoff


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Sampling.sample_packed := @_root_.OAI.AsymptoticallyMinimalLittlewood.Sampling.sample_packed

-- Prove2me | solution 1 for MasulloRH.unit_height_em_mesh_covers_logarithmic_edge_and_all_but_finitely_many_points
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T02:58:01.900849+00:00
-- url     : https://prove2.me/submissions/b8a7b0c3-7c65-4cd9-a2d6-528bb30ecf02

import Theorems.Thm_MasulloRH_rational_mesh_completes_unit_height_em_balls
import Theorems.Thm_MasulloRH_uniform_order_one_em_mesh_away_from_unit_height_zeros
import Theorems.Thm_SWPort_Davenport_zeta_zero_free_region
import Theorems.Thm_Zeta23_RvM_zeta_local_zero_count
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Set MasulloRH.UnitHeightMeshes

private def slab (n : ℕ) : Set ℂ := Complex.reProdIm (Icc (1/2) 1) (Icc (100000+(n:ℝ)) (100000+n+1))

private lemma in_slab (n k : ℕ) {s : ℂ} (hs : s ∈ rect n k) : s ∈ slab n ∧ 1/2 < s.re := by
  have pos : 0 < margin k := by unfold margin; positivity
  have re := hs.1.1
  have im := hs.2.1
  exact ⟨⟨⟨by linarith,hs.1.2⟩,⟨by linarith,hs.2.2⟩⟩,by linarith⟩

private lemma edge :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, ∀ s ∈ slab n, cutoff n c ≤ s.re → riemannZeta s ≠ 0 := by
  obtain ⟨c,hc,h⟩ := SWPort.Davenport.zeta_zero_free_region
  refine ⟨c,hc,fun n s hs hx => ?_⟩
  have lo := hs.2.1
  have hi := hs.2.2
  have hn := Nat.cast_nonneg (α:=ℝ) n
  have pos : 0 < s.im := by linarith
  have logp : 0 < Real.log (s.im+2) := Real.log_pos (by linarith)
  have lr : Real.log (s.im+2) ≤ Real.log ((100000:ℝ)+n+3) :=
    Real.log_le_log (by linarith) (by linarith)
  have hh : c / Real.log ((100000:ℝ)+n+3) ≤ c / Real.log (s.im+2) :=
    div_le_div_of_nonneg_left hc.le logp lr
  apply h s
  · intro eq
    rw [eq,Complex.one_im] at pos
    exact (lt_irrefl _ pos)
  · rw [abs_of_pos pos]
    exact (sub_le_sub_left hh 1).trans hx

private lemma from_interior (c : ℝ) (hc : 0 < c)
    (edgeOK : ∀ n : ℕ, ∀ s ∈ slab n, cutoff n c ≤ s.re → riemannZeta s ≠ 0)
    (h : innerMeshes) (n k : ℕ) (s : ℂ) (hs : s ∈ rect n k) : covered n k s := by
  by_cases outer : cutoff n c ≤ s.re
  · exact (MasulloRH.uniform_order_one_em_mesh_away_from_unit_height_zeros.1 n k s hs).2
      (edgeOK n s (in_slab n k hs).1 outer)
  obtain ⟨m,hm,tests⟩ := h c hc n k
  obtain ⟨i,hi,j,hj,left,near⟩ := MasulloRH.rational_mesh_completes_unit_height_em_balls.2.1 n k m hm s hs
  have pass := tests i hi j hj (left.trans_lt (lt_of_not_ge outer))
  exact ⟨node n k m i j,rad m,⟨MasulloRH.rational_mesh_completes_unit_height_em_balls.1 n k m i j hm hi hj,
    1,m,by decide,hm,pass⟩,near⟩

private lemma to_interior (all : ∀ n k : ℕ, ∀ s ∈ rect n k, covered n k s) : innerMeshes := by
  intro c hc n k
  have compact : IsCompact (rect n k) := isCompact_Icc.reProdIm isCompact_Icc
  have nz (s : ℂ) (hs : s ∈ rect n k) :=
    (MasulloRH.uniform_order_one_em_mesh_away_from_unit_height_zeros.1 n k s hs).1 (all n k s hs)
  obtain ⟨B,hB⟩ := MasulloRH.uniform_order_one_em_mesh_away_from_unit_height_zeros.2 n k (rect n k)
    compact (fun _ hx => hx) nz
  obtain ⟨pos,pass⟩ := hB B le_rfl
  refine ⟨B,pos,fun i hi j hj _ => pass i hi j hj ?_⟩
  refine ⟨_,MasulloRH.rational_mesh_completes_unit_height_em_balls.1 n k B i j pos hi hj,?_⟩
  simp only [dist_self,rad,Rat.cast_div,Rat.cast_ofNat,Rat.cast_natCast]
  positivity

private lemma count_le (T : ℝ) (F : Finset ℂ)
    (sub : ∀ z ∈ F, z ∈ Zeta23.zerosIn T (T+1)) : F.card ≤ Zeta23.Ncount T (T+1) := by
  classical
  have fin : (Zeta23.zerosIn T (T+1)).Finite := by
    have compact := (show IsCompact (Complex.reProdIm (Icc 0 1) (Icc T (T+1))) from
      isCompact_Icc.reProdIm isCompact_Icc).inter_riemannZetaZeros_finite
    apply compact.subset
    intro z hz
    exact ⟨⟨⟨hz.1.2.1.le,hz.1.2.2.le⟩,⟨hz.2.1.le,hz.2.2⟩⟩,mem_riemannZetaZeros.mpr hz.1.1⟩
  rw [Zeta23.Ncount,finsum_mem_eq_finite_toFinset_sum _ fin]
  calc
    F.card = ∑ z ∈ F, (1:ℕ) := by simp
    _ ≤ ∑ z ∈ F, Zeta23.zeroMult z := Finset.sum_le_sum fun z hz =>
      Zeta23.ZetaSeam.one_le_mult_holds z (sub z hz).1
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (fun z hz => fin.mem_toFinset.mpr (sub z hz))
      (fun _ _ _ => Nat.zero_le _)

private lemma horizontal_gap (F : Finset ℂ) (n : ℕ) :
    ∃ a b : ℚ, (100000:ℝ)+n+1/2 ≤ (a:ℝ) ∧ (b:ℝ) ≤ (100000:ℝ)+n+1 ∧
      (b:ℝ)-(a:ℝ) = 1/(4*((F.card:ℝ)+1)) ∧
      ∀ z ∈ F, z.im ∉ Icc (a:ℝ) (b:ℝ) := by
  classical
  let m := F.card+1
  let low : ℚ := 100000+(n:ℚ)+1/2
  let index (z : ℂ) := ⌊(z.im-(low:ℝ))*(2*(m:ℝ))⌋₊
  have cnt : (F.image index).card < (Finset.range m).card := by
    rw [Finset.card_range]
    exact Finset.card_image_le.trans_lt (Nat.lt_succ_self _)
  obtain ⟨j,hj,missing⟩ := Finset.exists_mem_notMem_of_card_lt_card cnt
  have jl : j < m := Finset.mem_range.mp hj
  have mp : 0 < m := Nat.succ_pos _
  have mp' : 0 < (m:ℝ) := by exact_mod_cast mp
  have jm : (j:ℝ)+1 ≤ (m:ℝ) := by exact_mod_cast jl
  let a : ℚ := low+(j:ℚ)/(2*m)
  let b : ℚ := a+1/(4*m)
  have ac : (a:ℝ) = (low:ℝ) + (j:ℝ)/(2*m) := by simp [a]
  have bc : (b:ℝ) = (a:ℝ) + 1/(4*m) := by simp [b]
  have loweq : (low:ℝ) = (100000:ℝ)+n+1/2 := by simp [low]
  have d1 : (0:ℝ) < 2*m := by positivity
  have d2 : (0:ℝ) < 4*m := by positivity
  have w : ((j:ℝ)/(2*m))*(2*m) = j := div_mul_cancel₀ _ d1.ne'
  have w' : (1/(4*(m:ℝ)))*(2*m) = 1/2 := by field_simp; ring
  have up : (j:ℝ)/(2*m)+1/(4*m) ≤ 1/2 := by
    apply (mul_le_mul_iff_left₀ d1).mp
    rw [add_mul,w,w']
    linarith
  refine ⟨a,b,?_,?_,?_,?_⟩
  · rw [ac,loweq]; exact le_add_of_nonneg_right (by positivity)
  · rw [bc,ac,loweq]; linarith
  · rw [bc]; simp [m]
  · intro z hz h
    have inlow := (mul_le_mul_iff_left₀ d1).2 h.1
    have inhi := (mul_le_mul_iff_left₀ d1).2 h.2
    rw [ac,add_mul,w] at inlow
    rw [bc,ac,add_mul,add_mul,w,w'] at inhi
    have lb : (j:ℝ) ≤ (z.im-(low:ℝ))*(2*m) := by rw [sub_mul]; linarith
    have ub : (z.im-(low:ℝ))*(2*m) < (j:ℝ)+1 := by rw [sub_mul]; linarith
    have id : index z = j := (Nat.floor_eq_iff ((Nat.cast_nonneg j).trans lb)).2 ⟨lb,ub⟩
    exact missing (Finset.mem_image.mpr ⟨z,hz,id⟩)

theorem solution :
    (∃ c A : ℝ, 0 < c ∧ 1 ≤ A ∧
      (∀ n k : ℕ, ∃ B : ℕ, ∀ m ≥ B, 0 < m ∧ ∀ i ≤ m, ∀ j ≤ m,
        (∃ s ∈ rect n k, cutoff n c ≤ s.re ∧
          dist s (rationalCenter (node n k m i j)) < (rad m:ℝ)) → passes n k m i j) ∧
      (∀ n : ℕ, ∃ E : Finset ℂ,
        (E.card:ℝ) ≤ A*Real.log ((100000:ℝ)+n+3) ∧
        (∀ z ∈ E, 1/2 < z.re ∧ z.re < cutoff n c ∧ riemannZeta z = 0) ∧
        (∀ k : ℕ, ∀ s ∈ rect n k, covered n k s ↔ s ∉ E) ∧
        ∃ a b : ℚ, (100000:ℝ)+n+1/2 ≤ (a:ℝ) ∧ (b:ℝ) ≤ (100000:ℝ)+n+1 ∧
          1/(4*(A*Real.log ((100000:ℝ)+n+3)+1)) ≤ (b:ℝ)-(a:ℝ) ∧
          ∀ k : ℕ, ∀ s ∈ rect n k, s.im ∈ Icc (a:ℝ) (b:ℝ) → covered n k s)) ∧
    (innerMeshes ↔ ∀ n k : ℕ, ∀ s ∈ rect n k, covered n k s) := by
  classical
  obtain ⟨c,hc,h⟩ := edge
  obtain ⟨A,hA,count⟩ := Zeta23.RvM.zeta_local_zero_count
  refine ⟨⟨c,A,hc,hA,?_,?_⟩,⟨from_interior c hc h,to_interior⟩⟩
  · intro n k
    let S := rect n k ∩ {z : ℂ | cutoff n c ≤ z.re}
    have compact : IsCompact S := (isCompact_Icc.reProdIm isCompact_Icc).inter_right
      (isClosed_le continuous_const Complex.continuous_re)
    obtain ⟨B,pass⟩ := MasulloRH.uniform_order_one_em_mesh_away_from_unit_height_zeros.2 n k S compact
      (fun z hz => hz.1) (fun z hz => h n z (in_slab n k hz.1).1 hz.2)
    refine ⟨B,fun m hm => ⟨(pass m hm).1,?_⟩⟩
    rintro i hi j hj ⟨s,hs,outer,near⟩
    exact (pass m hm).2 i hi j hj ⟨s,⟨hs,outer⟩,near⟩
  · intro n
    have finite := (show IsCompact (slab n) from isCompact_Icc.reProdIm isCompact_Icc).inter_riemannZetaZeros_finite
    let T : ℝ := 100000+(n:ℝ)
    let X := (slab n ∩ riemannZetaZeros) ∩ {z : ℂ | 1/2 < z.re ∧ T < z.im}
    have fin : X.Finite := finite.subset (fun z hz => hz.1)
    let E := fin.toFinset
    have facts (z : ℂ) (hz : z ∈ E) : 1/2 < z.re ∧ z.re < cutoff n c ∧ riemannZeta z = 0 := by
      have hx : z ∈ X := fin.mem_toFinset.mp hz
      have zero := mem_riemannZetaZeros.mp hx.1.2
      exact ⟨hx.2.1,lt_of_not_ge (fun le => h n z hx.1.1 le zero),zero⟩
    have bounded : (E.card:ℝ) ≤ A*Real.log (T+3) := by
      have le := count_le T E (fun z hz => by
        have hx : z ∈ X := fin.mem_toFinset.mp hz
        have z0 := (facts z hz).2.2
        have zr : z.re < 1 := lt_of_not_ge (fun h1 => riemannZeta_ne_zero_of_one_le_re h1 z0)
        exact ⟨⟨z0,by linarith [hx.2.1],zr⟩,hx.2.2,hx.1.1.2.2⟩)
      have nonneg : 0 ≤ T := by dsimp [T]; positivity
      exact (show (E.card:ℝ) ≤ (Zeta23.Ncount T (T+1):ℝ) by exact_mod_cast le).trans
        (by simpa [abs_of_nonneg nonneg] using count T)
    have represents (k : ℕ) (s : ℂ) (hs : s ∈ rect n k) : covered n k s ↔ s ∉ E := by
      have br := in_slab n k hs
      have gt : T < s.im := by
        have lo := hs.2.1
        have pos : 0 < margin k := by unfold margin; positivity
        dsimp [T]; linarith
      rw [MasulloRH.uniform_order_one_em_mesh_away_from_unit_height_zeros.1 n k s hs,fin.mem_toFinset]
      exact not_congr ⟨fun zero => ⟨⟨br.1,mem_riemannZetaZeros.mpr zero⟩,br.2,gt⟩,
        fun hx => mem_riemannZetaZeros.mp hx.1.2⟩
    obtain ⟨a,b,l,u,width,gap⟩ := horizontal_gap E n
    refine ⟨E,bounded,facts,represents,a,b,l,u,?_,?_⟩
    · rw [width]
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    · exact fun k s hs sw => (represents k s hs).2 (fun hin => gap s hin sw)

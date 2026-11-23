-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_packed_center_products_128_to_191
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:19:29.795811+00:00
-- url     : https://prove2.me/submissions/42f8c3f7-6a03-4f69-955a-8b56f469f79f

import Definitions.Def_GrothendieckLB_Supplement_cqHeadSumProducts
open GrothendieckLB.Supplement CQHeadArithmetic CQHeadCertificate CQHeadSum
set_option maxHeartbeats 150000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace ProductEvidence

private def seq (f : ℕ → ℤ) (n s : ℕ) : ℤ :=
  match n with
  | 0 => 0
  | m+1 => f s+base*seq f m (s+1)

private theorem seq_eq (f : ℕ → ℤ) (n s : ℕ) :
    seq f n s=pack base (fun k => f (s+k)) n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [seq,pack,ih]
    simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

private theorem rowFrom (a : ℕ) (h : row a=seq (wc a) 252 0*seq (pc a) 252 0)
    (hb : (List.range 252).all (good a)=true) : rowHolds a := by
  refine ⟨?_,hb⟩
  simpa only [seq_eq,Nat.zero_add,rowProduct] using h
private theorem row128 : rowHolds 128 := rowFrom 128 (by decide +kernel) (by decide +kernel)
private theorem row129 : rowHolds 129 := rowFrom 129 (by decide +kernel) (by decide +kernel)
private theorem row130 : rowHolds 130 := rowFrom 130 (by decide +kernel) (by decide +kernel)
private theorem row131 : rowHolds 131 := rowFrom 131 (by decide +kernel) (by decide +kernel)
private theorem row132 : rowHolds 132 := rowFrom 132 (by decide +kernel) (by decide +kernel)
private theorem row133 : rowHolds 133 := rowFrom 133 (by decide +kernel) (by decide +kernel)
private theorem row134 : rowHolds 134 := rowFrom 134 (by decide +kernel) (by decide +kernel)
private theorem row135 : rowHolds 135 := rowFrom 135 (by decide +kernel) (by decide +kernel)
private theorem row136 : rowHolds 136 := rowFrom 136 (by decide +kernel) (by decide +kernel)
private theorem row137 : rowHolds 137 := rowFrom 137 (by decide +kernel) (by decide +kernel)
private theorem row138 : rowHolds 138 := rowFrom 138 (by decide +kernel) (by decide +kernel)
private theorem row139 : rowHolds 139 := rowFrom 139 (by decide +kernel) (by decide +kernel)
private theorem row140 : rowHolds 140 := rowFrom 140 (by decide +kernel) (by decide +kernel)
private theorem row141 : rowHolds 141 := rowFrom 141 (by decide +kernel) (by decide +kernel)
private theorem row142 : rowHolds 142 := rowFrom 142 (by decide +kernel) (by decide +kernel)
private theorem row143 : rowHolds 143 := rowFrom 143 (by decide +kernel) (by decide +kernel)
private theorem row144 : rowHolds 144 := rowFrom 144 (by decide +kernel) (by decide +kernel)
private theorem row145 : rowHolds 145 := rowFrom 145 (by decide +kernel) (by decide +kernel)
private theorem row146 : rowHolds 146 := rowFrom 146 (by decide +kernel) (by decide +kernel)
private theorem row147 : rowHolds 147 := rowFrom 147 (by decide +kernel) (by decide +kernel)
private theorem row148 : rowHolds 148 := rowFrom 148 (by decide +kernel) (by decide +kernel)
private theorem row149 : rowHolds 149 := rowFrom 149 (by decide +kernel) (by decide +kernel)
private theorem row150 : rowHolds 150 := rowFrom 150 (by decide +kernel) (by decide +kernel)
private theorem row151 : rowHolds 151 := rowFrom 151 (by decide +kernel) (by decide +kernel)
private theorem row152 : rowHolds 152 := rowFrom 152 (by decide +kernel) (by decide +kernel)
private theorem row153 : rowHolds 153 := rowFrom 153 (by decide +kernel) (by decide +kernel)
private theorem row154 : rowHolds 154 := rowFrom 154 (by decide +kernel) (by decide +kernel)
private theorem row155 : rowHolds 155 := rowFrom 155 (by decide +kernel) (by decide +kernel)
private theorem row156 : rowHolds 156 := rowFrom 156 (by decide +kernel) (by decide +kernel)
private theorem row157 : rowHolds 157 := rowFrom 157 (by decide +kernel) (by decide +kernel)
private theorem row158 : rowHolds 158 := rowFrom 158 (by decide +kernel) (by decide +kernel)
private theorem row159 : rowHolds 159 := rowFrom 159 (by decide +kernel) (by decide +kernel)
private theorem row160 : rowHolds 160 := rowFrom 160 (by decide +kernel) (by decide +kernel)
private theorem row161 : rowHolds 161 := rowFrom 161 (by decide +kernel) (by decide +kernel)
private theorem row162 : rowHolds 162 := rowFrom 162 (by decide +kernel) (by decide +kernel)
private theorem row163 : rowHolds 163 := rowFrom 163 (by decide +kernel) (by decide +kernel)
private theorem row164 : rowHolds 164 := rowFrom 164 (by decide +kernel) (by decide +kernel)
private theorem row165 : rowHolds 165 := rowFrom 165 (by decide +kernel) (by decide +kernel)
private theorem row166 : rowHolds 166 := rowFrom 166 (by decide +kernel) (by decide +kernel)
private theorem row167 : rowHolds 167 := rowFrom 167 (by decide +kernel) (by decide +kernel)
private theorem row168 : rowHolds 168 := rowFrom 168 (by decide +kernel) (by decide +kernel)
private theorem row169 : rowHolds 169 := rowFrom 169 (by decide +kernel) (by decide +kernel)
private theorem row170 : rowHolds 170 := rowFrom 170 (by decide +kernel) (by decide +kernel)
private theorem row171 : rowHolds 171 := rowFrom 171 (by decide +kernel) (by decide +kernel)
private theorem row172 : rowHolds 172 := rowFrom 172 (by decide +kernel) (by decide +kernel)
private theorem row173 : rowHolds 173 := rowFrom 173 (by decide +kernel) (by decide +kernel)
private theorem row174 : rowHolds 174 := rowFrom 174 (by decide +kernel) (by decide +kernel)
private theorem row175 : rowHolds 175 := rowFrom 175 (by decide +kernel) (by decide +kernel)
private theorem row176 : rowHolds 176 := rowFrom 176 (by decide +kernel) (by decide +kernel)
private theorem row177 : rowHolds 177 := rowFrom 177 (by decide +kernel) (by decide +kernel)
private theorem row178 : rowHolds 178 := rowFrom 178 (by decide +kernel) (by decide +kernel)
private theorem row179 : rowHolds 179 := rowFrom 179 (by decide +kernel) (by decide +kernel)
private theorem row180 : rowHolds 180 := rowFrom 180 (by decide +kernel) (by decide +kernel)
private theorem row181 : rowHolds 181 := rowFrom 181 (by decide +kernel) (by decide +kernel)
private theorem row182 : rowHolds 182 := rowFrom 182 (by decide +kernel) (by decide +kernel)
private theorem row183 : rowHolds 183 := rowFrom 183 (by decide +kernel) (by decide +kernel)
private theorem row184 : rowHolds 184 := rowFrom 184 (by decide +kernel) (by decide +kernel)
private theorem row185 : rowHolds 185 := rowFrom 185 (by decide +kernel) (by decide +kernel)
private theorem row186 : rowHolds 186 := rowFrom 186 (by decide +kernel) (by decide +kernel)
private theorem row187 : rowHolds 187 := rowFrom 187 (by decide +kernel) (by decide +kernel)
private theorem row188 : rowHolds 188 := rowFrom 188 (by decide +kernel) (by decide +kernel)
private theorem row189 : rowHolds 189 := rowFrom 189 (by decide +kernel) (by decide +kernel)
private theorem row190 : rowHolds 190 := rowFrom 190 (by decide +kernel) (by decide +kernel)
private theorem row191 : rowHolds 191 := rowFrom 191 (by decide +kernel) (by decide +kernel)

end ProductEvidence
open ProductEvidence in
theorem solution : ∀ a : ℕ, 128 ≤ a → a < 192 → rowHolds a := by
  intro a hl hu
  by_cases h160 : a < 160
  ·
    by_cases h144 : a < 144
    ·
      by_cases h136 : a < 136
      ·
        by_cases h132 : a < 132
        ·
          rcases (show a=128 ∨ a=129 ∨ a=130 ∨ a=131 by omega) with rfl|rfl|rfl|rfl
          · exact row128
          · exact row129
          · exact row130
          · exact row131
        ·
          rcases (show a=132 ∨ a=133 ∨ a=134 ∨ a=135 by omega) with rfl|rfl|rfl|rfl
          · exact row132
          · exact row133
          · exact row134
          · exact row135
      ·
        by_cases h140 : a < 140
        ·
          rcases (show a=136 ∨ a=137 ∨ a=138 ∨ a=139 by omega) with rfl|rfl|rfl|rfl
          · exact row136
          · exact row137
          · exact row138
          · exact row139
        ·
          rcases (show a=140 ∨ a=141 ∨ a=142 ∨ a=143 by omega) with rfl|rfl|rfl|rfl
          · exact row140
          · exact row141
          · exact row142
          · exact row143
    ·
      by_cases h152 : a < 152
      ·
        by_cases h148 : a < 148
        ·
          rcases (show a=144 ∨ a=145 ∨ a=146 ∨ a=147 by omega) with rfl|rfl|rfl|rfl
          · exact row144
          · exact row145
          · exact row146
          · exact row147
        ·
          rcases (show a=148 ∨ a=149 ∨ a=150 ∨ a=151 by omega) with rfl|rfl|rfl|rfl
          · exact row148
          · exact row149
          · exact row150
          · exact row151
      ·
        by_cases h156 : a < 156
        ·
          rcases (show a=152 ∨ a=153 ∨ a=154 ∨ a=155 by omega) with rfl|rfl|rfl|rfl
          · exact row152
          · exact row153
          · exact row154
          · exact row155
        ·
          rcases (show a=156 ∨ a=157 ∨ a=158 ∨ a=159 by omega) with rfl|rfl|rfl|rfl
          · exact row156
          · exact row157
          · exact row158
          · exact row159
  ·
    by_cases h176 : a < 176
    ·
      by_cases h168 : a < 168
      ·
        by_cases h164 : a < 164
        ·
          rcases (show a=160 ∨ a=161 ∨ a=162 ∨ a=163 by omega) with rfl|rfl|rfl|rfl
          · exact row160
          · exact row161
          · exact row162
          · exact row163
        ·
          rcases (show a=164 ∨ a=165 ∨ a=166 ∨ a=167 by omega) with rfl|rfl|rfl|rfl
          · exact row164
          · exact row165
          · exact row166
          · exact row167
      ·
        by_cases h172 : a < 172
        ·
          rcases (show a=168 ∨ a=169 ∨ a=170 ∨ a=171 by omega) with rfl|rfl|rfl|rfl
          · exact row168
          · exact row169
          · exact row170
          · exact row171
        ·
          rcases (show a=172 ∨ a=173 ∨ a=174 ∨ a=175 by omega) with rfl|rfl|rfl|rfl
          · exact row172
          · exact row173
          · exact row174
          · exact row175
    ·
      by_cases h184 : a < 184
      ·
        by_cases h180 : a < 180
        ·
          rcases (show a=176 ∨ a=177 ∨ a=178 ∨ a=179 by omega) with rfl|rfl|rfl|rfl
          · exact row176
          · exact row177
          · exact row178
          · exact row179
        ·
          rcases (show a=180 ∨ a=181 ∨ a=182 ∨ a=183 by omega) with rfl|rfl|rfl|rfl
          · exact row180
          · exact row181
          · exact row182
          · exact row183
      ·
        by_cases h188 : a < 188
        ·
          rcases (show a=184 ∨ a=185 ∨ a=186 ∨ a=187 by omega) with rfl|rfl|rfl|rfl
          · exact row184
          · exact row185
          · exact row186
          · exact row187
        ·
          rcases (show a=188 ∨ a=189 ∨ a=190 ∨ a=191 by omega) with rfl|rfl|rfl|rfl
          · exact row188
          · exact row189
          · exact row190
          · exact row191
